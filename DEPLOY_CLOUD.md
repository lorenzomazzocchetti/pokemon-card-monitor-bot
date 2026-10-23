# Preparazione al passaggio su cloud

Il bot va eseguito come singolo servizio worker sempre attivo. Non avviare la
copia cloud con il token Telegram di produzione finché il bot locale è attivo:
le due istanze condividerebbero gli aggiornamenti Telegram e potrebbero fare
ricerche e inviare notifiche in parallelo.

## File già predisposti

- `Dockerfile`: installa le dipendenze e avvia `PokeBot.py`.
- `requirements.txt`: dipendenze Python bloccate alle versioni verificate.
- `.env.example`: nomi delle variabili da configurare come segreti nel provider.
- `BOT_DB_PATH=/data/bot_database.db`: destinazione sul disco persistente.

## Configurazione richiesta al provider

1. Crea un servizio Docker di tipo worker, con una sola istanza.
2. Collega un disco persistente montato in `/data`.
3. Configura le variabili presenti in `.env.example` nella sezione segreti.
   Non caricare né committare il file `.env` locale.
4. Prima della prova d'avvio, usa un bot Telegram di test e un database di test.
   Non usare il token di produzione mentre l'istanza locale è attiva.

## Passaggio finale

Quando la configurazione cloud è pronta e verificata:

1. Ferma il bot locale.
2. Copia il database finale sul disco persistente cloud. Se si genera uno
   snapshot mentre SQLite è attivo, usare l'API di backup SQLite; non copiare
   soltanto `bot_database.db` mentre sono presenti file WAL.
3. Imposta il token di produzione tra i segreti cloud e avvia una sola istanza.
4. Controlla i log, `/account`, il pannello admin e il primo ciclo scanner.
5. Mantieni il locale spento dopo la conferma. Per tornare indietro, ferma prima
   il cloud e riporta in locale il database aggiornato.

Il bot locale può restare attivo durante tutta la preparazione. Il database
caricato per la prova è solo un'istantanea e va aggiornato al momento del
passaggio finale.
