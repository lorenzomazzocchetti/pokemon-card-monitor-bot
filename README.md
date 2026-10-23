# Pokémon Card Listing Monitor

A Telegram bot that monitors eBay listings for Pokémon cards and sends matching offers to subscribers. Users can filter watches by card details and maximum price; administrators manage users and subscription packages.

## Features

- Search and monitor cards by name, card number, set, language, and budget
- Send matching eBay listings to Telegram users
- Manage subscription packages and per-card expiry dates
- Provide administrator workflows for accounts, subscriptions, and card watches
- Store bot data in SQLite, with a configurable database path for persistent cloud volumes
- Run as a Docker worker

## Stack

- Python 3.14
- `python-telegram-bot`
- eBay Browse API
- SQLite
- Docker

## Run locally

1. Create a virtual environment and install dependencies:

   ```powershell
   py -m venv .venv
   .\.venv\Scripts\Activate.ps1
   pip install -r requirements.txt
   ```

2. Copy `.env.example` to `.env` and set the required Telegram, eBay, and administrator values. Configure payment details only if you intend to enable the related bot features.

3. Start the bot:

   ```powershell
   python PokeBot.py
   ```

By default, the database is created at `bot_database.db`. Set `BOT_DB_PATH` to change its location.

## Run with Docker

Build the image and run it with a persistent data directory mounted at `/data`. Set the environment variables from `.env.example` in your deployment provider; do not copy `.env` into the image.

The included `Dockerfile` uses `/data/bot_database.db` as the default database path. For a production deployment, run a single worker instance with persistent storage so that the bot does not process Telegram updates or card searches twice.

See [DEPLOY_CLOUD.md](DEPLOY_CLOUD.md) for deployment and database migration notes.

## Tests

Run the existing test suite with:

```powershell
python -m unittest discover -s tests -v
```

## Configuration and data safety

- Keep `.env`, SQLite databases, backups, and generated files out of version control.
- `.env.example` contains variable names and placeholders only.
- Use test credentials and a test database when developing.
- Never run local and cloud production instances simultaneously with the same Telegram bot token.

## Disclaimer

This project is an independent community tool. It is not affiliated with, endorsed by, or sponsored by The Pokémon Company, Nintendo, or eBay. Pokémon is a trademark of its respective owners. Use of eBay APIs and listing data is subject to eBay's terms and developer policies.
