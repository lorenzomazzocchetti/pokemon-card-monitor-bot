import datetime
import tempfile
import unittest
from pathlib import Path

import PokeBot as bot


class SubscriptionPackageTests(unittest.TestCase):
    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.original_admin_chat_id = bot.ADMIN_CHAT_ID
        bot.DB_PATH = str(Path(self.temp_dir.name) / "test.sqlite3")
        bot.init_db()
        bot.db_ensure_user("test-user")

    def tearDown(self):
        bot.ADMIN_CHAT_ID = self.original_admin_chat_id
        self.temp_dir.cleanup()

    def _insert_card(self, package_id, name):
        with bot.db() as conn:
            return conn.execute("""
                INSERT INTO cards
                    (chat_id, card_name, card_number, set_name, keywords,
                     market_price, min_margin_pct, max_target_price, subscription_package_id)
                VALUES ('test-user', ?, '1/10', 'Test Set', ?, 0, 0, 10, ?)
            """, (name, name, package_id)).lastrowid

    def test_add_on_keeps_original_expiry_and_adds_capacity(self):
        first_end = bot.db_activate_subscription("test-user", 1, 6)
        with bot.db() as conn:
            package_id = conn.execute(
                "SELECT id FROM subscription_packages WHERE chat_id = 'test-user'"
            ).fetchone()[0]
        self._insert_card(package_id, "Card One")
        second_end = bot.db_activate_subscription("test-user", 1, 1)

        user = bot.db_get_user("test-user")
        self.assertEqual(user["card_limit"], 2)
        self.assertEqual(len(user["subscription_packages"]), 2)
        self.assertEqual(
            {p["subscription_end"] for p in user["subscription_packages"]},
            {first_end.isoformat(), second_end.isoformat()},
        )
        self.assertLess(second_end, first_end)

    def test_expiring_one_package_preserves_other_slots(self):
        bot.db_activate_subscription("test-user", 2, 6)
        with bot.db() as conn:
            package_id = conn.execute(
                "SELECT id FROM subscription_packages WHERE chat_id = 'test-user'"
            ).fetchone()[0]
        self._insert_card(package_id, "Card One")
        self._insert_card(package_id, "Card Two")
        expiring_end = bot.db_activate_subscription("test-user", 1, 1)
        with bot.db() as conn:
            expiring_package_id = conn.execute(
                "SELECT id FROM subscription_packages WHERE card_count = 1"
            ).fetchone()[0]
        self._insert_card(expiring_package_id, "Card Three")
        with bot.db() as conn:
            conn.execute(
                "UPDATE subscription_packages SET subscription_end = ? WHERE card_count = 1",
                ((datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(seconds=1)).isoformat(),),
            )

        self.assertEqual(bot.db_expire_overdue(), 1)
        user = bot.db_get_user("test-user")
        self.assertTrue(bot.db_subscription_is_active(user))
        self.assertEqual(user["card_limit"], 2)
        self.assertEqual(len(user["subscription_packages"]), 1)
        self.assertEqual(user["subscription_packages"][0]["card_count"], 2)
        self.assertLess(expiring_end, datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(days=31))

    def test_approved_payment_creates_one_separate_package(self):
        bot.db_activate_subscription("test-user", 1, 6)
        with bot.db() as conn:
            package_id = conn.execute(
                "SELECT id FROM subscription_packages WHERE chat_id = 'test-user'"
            ).fetchone()[0]
        self._insert_card(package_id, "Card One")
        request_token = bot.db_save_pending_payment("test-user", 1, 1, "tester", True)
        result = bot.db_approve_payment_request(request_token)

        self.assertTrue(result["ok"])
        user = bot.db_get_user("test-user")
        self.assertEqual(user["card_limit"], 2)
        self.assertEqual(len(user["subscription_packages"]), 2)
        self.assertIn(
            result["end"].isoformat(),
            {p["subscription_end"] for p in user["subscription_packages"]},
        )

    def test_legacy_subscription_migrates_without_extending_expiry(self):
        start = datetime.datetime.now(datetime.timezone.utc)
        end = start + datetime.timedelta(days=180)
        with bot.db() as conn:
            conn.execute("""
                UPDATE users SET plan = 'CUSTOM', subscription_status = 'ACTIVE',
                    subscription_start = ?, subscription_end = ?, card_limit = 3
                WHERE chat_id = 'test-user'
            """, (start.isoformat(), end.isoformat()))
            conn.execute("DROP TABLE subscription_packages")

        bot.init_db()
        user = bot.db_get_user("test-user")
        self.assertEqual(user["card_limit"], 3)
        self.assertEqual(len(user["subscription_packages"]), 1)
        self.assertEqual(user["subscription_packages"][0]["subscription_end"], end.isoformat())

    def test_startup_does_not_recreate_legacy_package_after_new_purchase(self):
        bot.db_activate_subscription("test-user", 1, 1)

        bot.init_db()

        with bot.db() as conn:
            packages = conn.execute(
                "SELECT source_key, status FROM subscription_packages WHERE chat_id = 'test-user'"
            ).fetchall()
        self.assertEqual(len(packages), 1)
        self.assertTrue(packages[0][0].startswith("purchase:"))

    def test_legacy_renewal_migrates_to_separate_scheduled_package(self):
        now = datetime.datetime.now(datetime.timezone.utc)
        start = now - datetime.timedelta(days=20)
        previous_end = now + datetime.timedelta(days=10)
        end = previous_end + datetime.timedelta(days=360)
        with bot.db() as conn:
            conn.execute("""
                UPDATE users SET plan = 'CUSTOM', subscription_status = 'ACTIVE',
                    subscription_start = ?, subscription_end = ?, card_limit = 2
                WHERE chat_id = 'test-user'
            """, (start.isoformat(), end.isoformat()))
        token = bot.db_save_pending_payment("test-user", 2, 12, "tester", True)
        with bot.db() as conn:
            conn.execute("""
                UPDATE payment_requests SET status = 'APPROVED', processed_at = ?
                WHERE request_token = ?
            """, (bot.time.time(), token))
            conn.execute("DROP TABLE subscription_packages")

        bot.init_db()
        user = bot.db_get_user("test-user")
        self.assertEqual(user["card_limit"], 2)
        self.assertEqual(len(user["subscription_packages"]), 2)
        self.assertEqual(user["subscription_packages"][0]["subscription_end"], previous_end.isoformat())
        self.assertEqual(user["subscription_packages"][1]["subscription_start"], previous_end.isoformat())
        self.assertEqual(user["subscription_packages"][1]["subscription_end"], end.isoformat())
        with bot.db() as conn:
            self.assertEqual(bot._max_reserved_subscription_capacity_on_conn(conn, "test-user"), 2)

    def test_legacy_cards_are_assigned_to_migrated_package(self):
        now = datetime.datetime.now(datetime.timezone.utc)
        end = now + datetime.timedelta(days=60)
        with bot.db() as conn:
            conn.execute("""
                UPDATE users SET plan = 'CUSTOM', subscription_status = 'ACTIVE',
                    subscription_start = ?, subscription_end = ?, card_limit = 2
                WHERE chat_id = 'test-user'
            """, (now.isoformat(), end.isoformat()))
            conn.execute("DROP TABLE subscription_packages")
            conn.executemany("""
                INSERT INTO cards
                    (chat_id, card_name, card_number, set_name, keywords,
                     market_price, min_margin_pct, max_target_price)
                VALUES ('test-user', ?, '1/10', 'Test Set', ?, 0, 0, 10)
            """, [("Card One", "Card One"), ("Card Two", "Card Two")])

        bot.init_db()
        self.assertEqual(len(bot.db_get_monitored_user_cards("test-user")), 2)

    def test_total_active_capacity_cannot_exceed_limit(self):
        bot.db_activate_subscription("test-user", bot.MAX_USER_CARDS, 1)
        with bot.db() as conn:
            package_id = conn.execute(
                "SELECT id FROM subscription_packages WHERE chat_id = 'test-user'"
            ).fetchone()[0]
            conn.executemany("""
                INSERT INTO cards
                    (chat_id, card_name, card_number, set_name, keywords,
                     market_price, min_margin_pct, max_target_price, subscription_package_id)
                VALUES ('test-user', ?, '1/10', 'Test Set', ?, 0, 0, 10, ?)
            """, [(f"Card {i}", f"Card {i}", package_id) for i in range(bot.MAX_USER_CARDS)])
        with self.assertRaises(ValueError):
            bot.db_activate_subscription("test-user", 1, 1)

    def test_pending_payment_approval_rechecks_free_slots(self):
        bot.db_activate_subscription("test-user", 2, 6)
        token = bot.db_save_pending_payment("test-user", 1, 1, "tester", True)

        result = bot.db_approve_payment_request(token)

        self.assertFalse(result["ok"])
        self.assertIn("slot liberi", result["message"])
        self.assertEqual(len(bot.db_get_user("test-user")["subscription_packages"]), 1)

    def test_manual_deactivation_suppresses_expiry_upsell_notice(self):
        end = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(hours=1)
        start = end - datetime.timedelta(days=30)
        with bot.db() as conn:
            conn.execute("""
                INSERT INTO subscription_packages
                    (source_key, chat_id, card_count, subscription_start, subscription_end,
                     status, created_at)
                VALUES ('expired', 'test-user', 1, ?, ?, 'EXPIRED', ?)
            """, (start.isoformat(), end.isoformat(), bot.time.time()))
            conn.execute("""
                INSERT INTO subscription_packages
                    (source_key, chat_id, card_count, subscription_start, subscription_end,
                     status, created_at)
                VALUES ('active', 'test-user', 1, ?, ?, 'ACTIVE', ?)
            """, (end.isoformat(), (end + datetime.timedelta(days=30)).isoformat(), bot.time.time()))

        bot.db_deactivate_subscription("test-user")

        self.assertEqual(bot.db_users_to_notify_expired(), [])

    def test_purchase_gate_requires_every_current_slot_to_be_used(self):
        bot.db_activate_subscription("test-user", 2, 6)
        self.assertFalse(bot._can_buy_another_package("test-user"))
        with bot.db() as conn:
            package_id = conn.execute(
                "SELECT id FROM subscription_packages WHERE chat_id = 'test-user'"
            ).fetchone()[0]
        self._insert_card(package_id, "Card One")
        self.assertIn("Coperta fino al", bot.db_get_user_cards("test-user")[0]["coverage_text"])
        self.assertFalse(bot._can_buy_another_package("test-user"))
        self._insert_card(package_id, "Card Two")
        self.assertTrue(bot._can_buy_another_package("test-user"))

    def test_duplicate_cards_do_not_consume_a_second_slot(self):
        bot.db_activate_subscription("test-user", 2, 6)
        result = bot.db_add_card("test-user", "Pikachu", "1/10", "Test Set", "ENG", 10, 2)
        self.assertTrue(result)
        with self.assertRaisesRegex(ValueError, "già nel tuo Pokédex"):
            bot.db_add_card("test-user", "pikachu", "1/10", "test set", "eng", 10, 2)
        self.assertEqual(len(bot.db_get_monitored_user_cards("test-user")), 1)

    def test_admin_card_field_updates_validate_and_persist_all_fields(self):
        bot.db_activate_subscription("test-user", 1, 6)
        bot.db_add_card("test-user", "Pikachu", "1/10", "Test Set", "ENG", 10, 2)
        card = bot.db_get_user_cards("test-user")[0]

        bot.db_update_card_field("test-user", card["id"], "name", "Raichu")
        bot.db_update_card_field("test-user", card["id"], "number", "2/10")
        bot.db_update_card_field("test-user", card["id"], "set", "Updated Set")
        bot.db_update_card_field("test-user", card["id"], "language", "ita")
        bot.db_update_card_field("test-user", card["id"], "price", "25.50")

        updated = bot.db_get_card("test-user", card["id"])
        self.assertEqual(updated["name"], "Raichu")
        self.assertEqual(updated["card_number"], "2/10")
        self.assertEqual(updated["set_name"], "Updated Set")
        self.assertEqual(updated["language"], "ITA")
        self.assertEqual(updated["max_target_price_eur"], 25.5)
        with self.assertRaises(ValueError):
            bot.db_update_card_field("test-user", card["id"], "language", "not-a-language")
        with self.assertRaises(ValueError):
            bot.db_update_card_field("test-user", card["id"], "name", "not a Pokemon")

    def test_admin_card_field_update_rejects_duplicate_identity(self):
        bot.db_activate_subscription("test-user", 2, 6)
        bot.db_add_card("test-user", "Pikachu", "1/10", "Test Set", "ENG", 10, 2)
        bot.db_add_card("test-user", "Raichu", "2/10", "Test Set", "ENG", 10, 2)
        cards = bot.db_get_user_cards("test-user")

        bot.db_update_card_field("test-user", cards[1]["id"], "number", "1/10")
        with self.assertRaisesRegex(ValueError, "duplicherebbe"):
            bot.db_update_card_field("test-user", cards[1]["id"], "name", "Pikachu")

    def test_expired_package_stops_only_cards_assigned_to_it(self):
        bot.db_activate_subscription("test-user", 1, 6)
        with bot.db() as conn:
            first_package_id = conn.execute(
                "SELECT id FROM subscription_packages WHERE chat_id = 'test-user'"
            ).fetchone()[0]
        first_card = self._insert_card(first_package_id, "Card One")
        bot.db_activate_subscription("test-user", 1, 1)
        with bot.db() as conn:
            packages = conn.execute(
                "SELECT id, card_count FROM subscription_packages WHERE chat_id = 'test-user' ORDER BY id"
            ).fetchall()
        second_card = self._insert_card(packages[1][0], "Card Two")
        with bot.db() as conn:
            conn.execute(
                "UPDATE subscription_packages SET subscription_end = ? WHERE id = ?",
                ((datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(seconds=1)).isoformat(), packages[1][0]),
            )

        self.assertEqual(bot.db_expire_overdue(), 1)
        monitored_ids = {card["id"] for card in bot.db_get_monitored_user_cards("test-user")}
        self.assertEqual(monitored_ids, {first_card})
        with bot.db() as conn:
            self.assertIsNone(conn.execute(
                "SELECT subscription_package_id FROM cards WHERE id = ?", (second_card,)
            ).fetchone()[0])

    def test_card_assignment_rolls_forward_to_scheduled_renewal(self):
        start = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=31)
        boundary = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(seconds=1)
        renewal_end = boundary + datetime.timedelta(days=30)
        with bot.db() as conn:
            base_id = conn.execute("""
                INSERT INTO subscription_packages
                    (source_key, chat_id, card_count, subscription_start, subscription_end,
                     status, created_at)
                VALUES ('base', 'test-user', 1, ?, ?, 'ACTIVE', ?)
            """, (start.isoformat(), boundary.isoformat(), bot.time.time())).lastrowid
            renewal_id = conn.execute("""
                INSERT INTO subscription_packages
                    (source_key, chat_id, card_count, subscription_start, subscription_end,
                     status, created_at)
                VALUES ('renewal', 'test-user', 1, ?, ?, 'ACTIVE', ?)
            """, (boundary.isoformat(), renewal_end.isoformat(), bot.time.time())).lastrowid
        card_id = self._insert_card(base_id, "Card One")

        self.assertEqual(bot.db_expire_overdue(), 1)
        self.assertEqual([card["id"] for card in bot.db_get_monitored_user_cards("test-user")], [card_id])
        with bot.db() as conn:
            self.assertEqual(conn.execute(
                "SELECT subscription_package_id FROM cards WHERE id = ?", (card_id,)
            ).fetchone()[0], renewal_id)

    def test_admin_cards_without_packages_are_monitored_and_can_be_paused(self):
        bot.ADMIN_CHAT_ID = "test-user"
        first = self._insert_card(None, "Pikachu")
        second = self._insert_card(None, "Raichu")

        all_users = bot.db_get_all_users_data()
        self.assertEqual(
            {card["id"] for card in all_users["test-user"]["target_cards"]},
            {first, second},
        )
        self.assertTrue(bot.db_set_card_monitoring("test-user", first, False))
        cards = bot.db_get_user_cards("test-user")
        self.assertEqual(cards[0]["coverage_text"], "Monitoraggio in pausa")
        self.assertFalse(cards[0]["is_monitored"])
        self.assertEqual(
            {card["id"] for card in bot.db_get_all_users_data()["test-user"]["target_cards"]},
            {second},
        )
        self.assertTrue(bot.db_set_card_monitoring("test-user", first, True))
        self.assertEqual(len(bot.db_get_all_users_data()["test-user"]["target_cards"]), 2)

        keyboard = bot.pokedex_keyboard(
            [(0, [{"id": first, "monitoring_enabled": False}])], 0, "test-user"
        )
        callbacks = [button.callback_data for row in keyboard.inline_keyboard for button in row]
        self.assertIn(f"admin:cardmon:{first}:1:0", callbacks)
        self.assertIn(f"admin:carddel:ask:{first}:0", callbacks)

    def test_admin_can_delete_own_card_without_deleting_other_users_cards(self):
        bot.ADMIN_CHAT_ID = "test-user"
        card_id = self._insert_card(None, "Pikachu")

        self.assertFalse(bot.db_delete_card("other-user", card_id))
        self.assertTrue(bot.db_delete_card("test-user", card_id))
        self.assertEqual(bot.db_get_user_cards("test-user"), [])

    def test_first_monitoring_migration_deletes_existing_admin_cards_only(self):
        bot.ADMIN_CHAT_ID = "test-user"
        self._insert_card(None, "Pikachu")
        self._insert_card(None, "Raichu")
        bot.db_ensure_user("other-user")
        with bot.db() as conn:
            conn.execute("""
                INSERT INTO cards
                    (chat_id, card_name, card_number, set_name, keywords,
                     market_price, min_margin_pct, max_target_price)
                VALUES ('other-user', 'Eevee', '3/10', 'Test Set', 'Eevee', 0, 0, 10)
            """)
        with bot.db() as conn:
            conn.execute("ALTER TABLE cards DROP COLUMN monitoring_enabled")

        bot.init_db()

        self.assertEqual(bot.db_get_user_cards("test-user"), [])
        self.assertEqual(bot.db_get_monitored_user_cards("test-user"), [])
        with bot.db() as conn:
            self.assertEqual(conn.execute("SELECT COUNT(*) FROM cards").fetchone()[0], 1)
            self.assertEqual(conn.execute("SELECT COUNT(*) FROM cards WHERE chat_id = 'other-user'").fetchone()[0], 1)


if __name__ == "__main__":
    unittest.main()
