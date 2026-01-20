# Report FOSSA – Vulnerabilità e Gestione delle Dipendenze

## 1. Vulnerabilità individuata e risoluzione

Durante l’analisi del repository tramite **FOSSA (scan online)** è stata individuata una vulnerabilità di livello **HIGH (CVSS 7.5)**, identificata come **CVE-2025-15284**, presente nella libreria `qs` versione 6.13.0, utilizzata come dipendenza transitiva del server Node.js.

La vulnerabilità riguarda un problema di **Improper Input Validation** nel modulo di parsing delle query string: in particolare, l’opzione di sicurezza `arrayLimit` non viene applicata correttamente alla **bracket notation** (`a[]=value`). Questo comportamento consente a un attaccante di inviare richieste HTTP appositamente costruite in grado di causare **Denial of Service (DoS)** tramite esaurimento della memoria del server, anche senza autenticazione.

La dipendenza `qs` non era dichiarata direttamente nel `package.json`, ma veniva introdotta indirettamente da **Express** e librerie correlate. Per questo motivo la vulnerabilità non era immediatamente visibile tramite l’analisi diretta delle dipendenze principali.

### Risoluzione

La vulnerabilità è stata risolta forzando l’aggiornamento della dipendenza transitiva `qs` alla versione **6.14.1**, che include il fix ufficiale.  
L’aggiornamento è stato applicato utilizzando la funzionalità `overrides` di npm, aggiungendo la  configurazione nel file `package.json` del modulo `node_server`.

## 2. Denied Licenses – JMH Dependencies

Le dipendenze transitive `org.openjdk.jmh:jmh-core` e `org.openjdk.jmh:jmh-generator-annprocess` riportano licenza **GPL-2.0 WITH Classpath Exception**, contraria alla policy FOSSA.

### Analisi
Entrambe le librerie sono dichiarate nel `pom.xml` con `<scope>test>` e vengono utilizzate solo per **test e generazione di codice**, senza essere incluse nell’artefatto finale distribuito. La licenza non influisce quindi sulla distribuzione del software.

### Risoluzione
Le licenze sono state accettate/override in **FOSSA**, con la motivazione che:
- Le librerie sono utilizzate esclusivamente a fini di testing;
- Non influiscono sulla distribuzione del progetto;
- La policy interna consente l’utilizzo in questo contesto senza modifiche al codice principale.

**Conclusione:** Le segnalazioni Denied License relative a JMH sono state giustificate e ignorate, in quanto non critiche per la distribuzione del progetto.

## 3. Outdated Dependencies

### 3.1 JUnit Platform Launcher
- **Dipendenza:** `org.junit.platform:junit-platform-launcher`  
- **Versione attuale:** 1.11.4  
- **Ultima versione disponibile:** 6.0.2  
- **Valutazione:** Dipendenza transitiva obsoleta; aggiornamento pianificato.  
  Attualmente non impatta il codice in produzione.

### 3.2 mime
- **Dipendenza:** `mime`  
- **Versione attuale:** 1.6.0  
- **Ultima versione disponibile:** 4.1.0  
- **Valutazione:** Dipendenza transitiva obsoleta; aggiornamento consigliato.  
  Non influisce sul codice in produzione.

### 3.3 path-to-regexp
- **Dipendenza:** `path-to-regexp`  
- **Versione attuale:** 0.1.12  
- **Ultima versione disponibile:** 8.3.0  
- **Valutazione:** Dipendenza transitiva obsoleta; aggiornamento consigliato.  
  Non influisce sul codice in produzione.

---

## 4. Gestione delle Flagged Dependencies e Licenza del Progetto

Durante l’analisi tramite **FOSSA**, il progetto **UniClass-Sustainable** ha generato 39 segnalazioni relative a dipendenze esterne, suddivise principalmente in due categorie:

### 4.1 Librerie Java / Jakarta (26 issues)
- **Licenze:** EPL-2.0, GPL-2.0-with-classpath-exception  
- **Valutazione:** Librerie standard non modificate; le licenze EPL e GPL-2.0-with-classpath-exception permettono l’uso come librerie esterne senza obbligo di rilasciare il codice del progetto.  
- **Azione:** Segnalazioni considerate non critiche e ignorate.

### 4.2 Librerie Immagini / Sharp (12 issues)
- **Licenze:** LGPL-3.0  
- **Valutazione:** Librerie Sharp utilizzate come dipendenze esterne non modificate. LGPL-3.0 impone restrizioni solo in caso di modifica o integrazione statica.  
- **Azione:** Segnalazioni considerate non critiche e ignorate.

### 4.3 Licenza del progetto
Il progetto è rilasciato sotto **licenza ISC**, una licenza permissiva simile alla MIT, che permette la ridistribuzione e l’uso libero del codice senza vincoli virali.  
- Il file `package.json` dichiara esplicitamente `"license": "ISC"`.  
- Eventuali file precedenti con licenze GNU GPL sono stati rimossi per garantire coerenza con la licenza permissiva scelta.

**Conclusione:**  
Tutte le flagged dependencies sono librerie esterne standard, non modificate, e compatibili con la licenza ISC del progetto. Non sono necessarie ulteriori azioni correttive.

