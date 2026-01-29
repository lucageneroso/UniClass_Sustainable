# Report Finale sulle Issue Statiche: Analisi, Classificazione e Motivazioni Tecniche

L’analisi statica condotta sul progetto UniClass ha permesso di individuare un insieme articolato di segnalazioni provenienti sia dalle regole della suite Creedengo sia dalle regole di SonarJava. L’obiettivo di questo report è fornire una valutazione complessiva delle issue rilevate, distinguendo tra quelle effettivamente indicative di un problema e quelle che, per ragioni tecniche, architetturali o di specifica, devono essere classificate come falsi positivi. L’intero processo è stato affrontato con un approccio sistematico, volto a garantire coerenza, sostenibilità del codice e aderenza alle best practice delle tecnologie utilizzate.

## 1. Considerazioni generali sulle regole analizzate

Una parte significativa delle segnalazioni riguarda la regola Creedengo GCI82, che suggerisce di dichiarare come `final` le variabili non riassegnate. Tale regola è concepita per variabili locali all’interno dei metodi, ma è stata applicata in numerosi contesti non pertinenti, come parametri di metodi e costruttori, campi JPA, campi CDI/EJB e parametri delle servlet. In tali casi, l’aggiunta del modificatore `final` non apporta alcun beneficio in termini di sicurezza o manutenibilità e, in alcuni scenari, risulta incompatibile con il ciclo di vita degli oggetti gestiti dal container. Per questo motivo, tali segnalazioni sono state classificate come falsi positivi.

La regola Creedengo GCI32, relativa all’inizializzazione di `StringBuilder` con una capacità appropriata, è risultata correttamente applicabile nei casi in cui la lunghezza della stringa risultante era nota a priori. La modifica è stata quindi recepita.

La regola Creedengo GCI67, che suggerisce l’uso del pre-incremento nei cicli `for`, è stata applicata nei pochi casi in cui era pertinente, senza alterare il comportamento del codice.

La regola SonarJava S1948, che richiede che i campi di una classe serializzabile siano anch’essi serializzabili o dichiarati `transient`, ha generato numerosi falsi positivi. Le servlet non vengono serializzate dal container, i campi EJB non devono essere serializzabili e le entity JPA, pur implementando `Serializable`, non richiedono che i loro campi lo siano, poiché gestiti tramite proxy dal persistence provider. In tutti questi casi, la regola non è applicabile.

## 2. Tabella riepilogativa delle issue analizzate

| File | Regola | Elemento coinvolto | Stato | Motivazione sintetica |
|------|--------|---------------------|--------|------------------------|
| HomeRedirectFilter | GCI82 | Variabili locali | Risolta | Variabili non riassegnate, `final` applicabile |
| DatabasePopulator | GCI82 | Variabili locali | Risolta | Applicazione corretta della regola |
| DatabaseProducer | GCI82 | Campo CDI/JPA | False Positive | Campo iniettato, non può essere `final` |
| AlreadyExistentUserException | GCI82 | Parametro costruttore | False Positive | Parametri non sono variabili locali |
| PasswordGenerator | GCI82 | Variabili locali | Risolta | Applicazione corretta |
| PasswordGenerator | GCI32 | StringBuilder | Risolta | Capacità nota, ottimizzazione valida |
| PasswordGenerator | GCI67 | Incremento nel ciclo | Risolta | Pre-incremento preferibile |
| PasswordGenerator.shuffleString | GCI82 | Parametri metodo | False Positive | Parametri non riassegnati, `final` inutile |
| Messaggio (entity) | GCI82 | Campi JPA | False Positive | JPA richiede mutabilità dei campi |
| MessaggioDAO | GCI82 | Campo EntityManager | False Positive | CDI/JPA injection |
| MessaggioDAO | GCI82 | Parametri metodo | False Positive | Regola non applicabile |
| MessaggioDAO | GCI82 | Variabili locali | Facoltativa | Applicabile ma non necessaria |
| EdificioServlet | GCI82 | Parametri servlet | False Positive | Servlet API non usa `final` sui parametri |
| ConversazioniServlet | S1948 | Campo EJB | False Positive | EJB non serializzabile, gestito dal container |
| Aula (entity) | GCI82 | Campi JPA | False Positive | Mutabilità richiesta dal persistence provider |
| Docente (entity) | S1948 | Campi JPA | False Positive | Proxy JPA non serializzabili |
| Docente (entity) | GCI82 | Campi JPA | False Positive | Regola non applicabile |

## 3. Conclusioni

L’analisi complessiva mostra come una parte rilevante delle segnalazioni derivi da un’applicazione non contestualizzata delle regole di analisi statica. In particolare, le regole GCI82 e S1948 tendono a generare falsi positivi in presenza di tecnologie come JPA, CDI, EJB e Servlet API, le quali prevedono cicli di vita e modalità di gestione dei campi incompatibili con le assunzioni alla base delle regole stesse. L’intervento correttivo è stato quindi limitato ai soli casi in cui la regola risultava effettivamente applicabile e utile, evitando modifiche superflue o potenzialmente dannose.

Il risultato finale è un codice più coerente, sostenibile e conforme alle best practice, accompagnato da una documentazione chiara che giustifica ogni scelta effettuata. Questo approccio ha permesso di mantenere un equilibrio tra rigore formale, correttezza architetturale e sostenibilità del software, garantendo al tempo stesso una tracciabilità completa delle decisioni prese durante il processo di revisione.
