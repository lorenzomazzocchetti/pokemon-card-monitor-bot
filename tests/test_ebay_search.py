import unittest
from unittest.mock import patch

import PokeBot as bot


class EbaySearchTests(unittest.TestCase):
    def test_search_includes_card_name_number_and_set_but_not_language(self):
        card = {
            "id": 901,
            "name": "Sabrina's Gengar Banned",
            "card_number": "094",
            "set_name": "Gym Challenge",
            "keywords": "Sabrina's Gengar Banned Gym Challenge 094 JAP",
            "max_target_price_eur": 5000,
        }
        response = type("Response", (), {
            "status_code": 200,
            "json": lambda self: {"itemSummaries": []},
        })()

        with patch.object(bot.requests, "get", return_value=response) as get:
            result = bot.search_ebay_deals("token", card, "test-user")

        self.assertEqual(result, "ok")
        query = get.call_args.kwargs["params"]["q"]
        self.assertIn("Sabrina's Gengar Banned 094 Gym Challenge", query)
        self.assertNotIn("JAP", query)

    def test_search_requires_the_requested_pokemon_species(self):
        card = {"name": "Sabrina's Gengar Banned"}

        self.assertTrue(bot._listing_matches_requested_card(
            {"title": "Sabrina's Gengar Japanese Pokémon card"}, card
        ))
        self.assertFalse(bot._listing_matches_requested_card(
            {"title": "Sabrina's Pikachu Japanese Pokémon card"}, card
        ))


    def test_listing_must_match_requested_set_and_number(self):
        card = {"name": "Charizard", "card_number": "4/102", "set_name": "Set Base"}

        self.assertTrue(bot._listing_matches_requested_card(
            {"title": "Pokemon Charizard Base Set Holo 4/102"}, card
        ))
        self.assertFalse(bot._listing_matches_requested_card(
            {"title": "Pokemon Charizard Jungle Holo 4/102"}, card
        ))
        self.assertFalse(bot._listing_matches_requested_card(
            {"title": "Pokemon Charizard Base Set Holo 5/102"}, card
        ))

    def test_listing_without_requested_set_or_number_is_not_accepted(self):
        card = {"name": "Charizard", "card_number": "4/102", "set_name": "Base Set"}

        self.assertFalse(bot._listing_matches_requested_card(
            {"title": "Pokemon Charizard Holo card"}, card
        ))



if __name__ == "__main__":
    unittest.main()
