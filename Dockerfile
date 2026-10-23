FROM python:3.14-slim

WORKDIR /app

COPY requirements.txt ./
RUN pip install --no-cache-dir -r requirements.txt

COPY PokeBot.py pokemon_names.txt ./

ENV BOT_DB_PATH=/data/bot_database.db

CMD ["python", "PokeBot.py"]
