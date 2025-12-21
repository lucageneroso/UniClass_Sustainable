package it.unisa.uniclass.orari.model;

import it.unisa.uniclass.utenti.model.Docente;
import jakarta.persistence.*;

import java.io.Serializable;
import java.sql.Time;
import java.util.List;
import java.util.ArrayList;


/**
 * Rappresenta una lezione nel sistema di gestione orari.
 * Contiene informazioni come la data, l'orario, il giorno, il corso associato, l'aula e altre proprietà rilevanti.
 * */

@Entity
@Access(AccessType.FIELD)
@Table(name = "lezioni")
@NamedQueries({
        @NamedQuery(name = "Lezione.trovaLezione", query = "SELECT l FROM Lezione l WHERE l.id = :id"),
        @NamedQuery(name = "Lezione.trovaLezioneCorso", query = "SELECT l FROM Lezione l WHERE l.corso.nome = :nomeCorso"),
        @NamedQuery(name = "Lezione.trovaLezioneOre", query = "SELECT l FROM Lezione l WHERE l.oraInizio = :oraInizio AND l.oraFine = :oraFine"),
        @NamedQuery(name = "Lezione.trovaLezioneOreGiorno", query = "SELECT l FROM Lezione l WHERE l.giorno = :giorno AND l.oraInizio = :oraInizio AND l.oraFine = :oraFine"),
        @NamedQuery(name = "Lezione.trovaLezioneAula", query = "SELECT l FROM Lezione l WHERE l.aula.nome = :nome"),
        @NamedQuery(name = "Lezione.trovaTutte", query = "SELECT l FROM Lezione l"),
        @NamedQuery(name = "Lezione.trovaLezioneCorsoRestoAnno",
                query = "SELECT l FROM Lezione l " +
                        "JOIN l.corso c " +
                        "JOIN c.corsoLaurea cl " +
                        "JOIN l.resto r " +
                        "JOIN c.annoDidattico a " +
                        "WHERE cl.id = :corsoLaureaId " +
                        "AND r.id = :restoId " +
                        "AND a.id = :annoId"),
        @NamedQuery(name = "Lezione.trovaLezioneCorsoRestoAnnoSemestre", query = "SELECT l FROM Lezione l " +
                "JOIN l.corso c " +
                "JOIN c.corsoLaurea cl " +
                "JOIN l.resto r " +
                "JOIN c.annoDidattico a " +
                "WHERE cl.id = :corsoLaureaId " +
                "AND r.id = :restoId " +
                "AND a.id = :annoId AND l.semestre = :semestre"),
        @NamedQuery(name = "Lezione.trovaLezioniDocente", query = "SELECT l FROM Lezione l JOIN l.docenti d WHERE d.nome = :nomeDocente")
})
public class Lezione implements Serializable {

    /**
     * Query per trovare una lezione tramite ID
     * */
    public static final  String TROVA_LEZIONE = "Lezione.trovaLezione";
    /**
     * Query per trovare lezioni associate a un corso specifico.
     * */
    public static final  String TROVA_LEZIONE_CORSO = "Lezione.trovaLezioneCorso";
    /**
     * Query per trovare lezioni in base all'orario di inizio e fine.
     * */
    public static final  String TROVA_LEZIONE_ORE = "Lezione.trovaLezioneOre";
    /**
     * Query per trovare lezioni in base all'orario e al giorno
     * */
    public static final String TROVA_LEZIONE_ORE_GIORNO = "Lezione.trovaLezioneOreGiorno";
    /**
     * Query per trovare lezioni in base all'aula
     * */
    public static final String TROVA_LEZIONE_AULA = "Lezione.trovaLezioneAula";
    /**
     * Query per trovare tutte le lezioni.
     * */
    public static final String TROVA_TUTTE = "Lezione.trovaTutte";
    /**
     * Query per trovare lezioni in base al corso, resto e anno.
     * */
    public static final String TROVA_LEZIONE_CORSO_RESTO_ANNO = "Lezione.trovaLezioneCorsoRestoAnno";
    /**
     * Query per trovare lezioni in base al corso, resto, anno e semestre.
     * */
    public static final String TROVA_LEZIONE_CORSO_RESTO_ANNO_SEMESTRE = "Lezione.trovaLezioneCorsoRestoAnnoSemestre";
    /**
     * Query per trovare lezioni di uno specifico docente.
     * */
    public static final String TROVA_LEZIONI_DOCENTE = "Lezione.trovaLezioniDocente";

    /**
     * Identificativo univoco per Lezione
     */
    @Id @GeneratedValue(strategy = GenerationType.IDENTITY)
    //@ spec_public
    //@ nullable
    private Long id;

    /**
     * Lista dei docenti che presenziano la lezione
     */
    @ManyToMany(mappedBy = "lezioni")
    //@ spec_public
    //@ nullable
    private List<Docente> docenti = new ArrayList<>();

    /**
     * Semestre in cui è presente la lezione
     */
    //@ spec_public
    private int semestre; //1 o 2

    /**
     * Ora di Inizio della Lezione
     */
    //@ spec_public
    //@ nullable
    private Time oraInizio;

    /**
     * Ora di Fine della lezione
     */
    //@ spec_public
    //@ nullable
    private Time oraFine;

    /**
     * Giorno della settimana in cui si sostiene la lezione (Tramite Enumeratore)
     */
    @Enumerated(EnumType.STRING)
    //@ spec_public
    //@ nullable
    private Giorno giorno;

    /**
     * Corso della lezione
     */
    @ManyToOne
    @JoinColumn(name = "corso_id")
    //@ spec_public
    //@ nullable
    private Corso corso;

    /**
     * Resto o Sezione della classe che segue la lezione
     */
    @ManyToOne
    @JoinColumn(name = "resto_id")
    //@ spec_public
    //@ nullable
    private Resto resto;

    /**
     * Aula in cui è presente la lezione
     */
    @ManyToOne(cascade = CascadeType.PERSIST)
    @JoinColumn(name = "aula_id")
    //@ spec_public
    //@ nullable
    private Aula aula;

    /**
     *
     * Costruttore predefinito.
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing; //NOSONAR
      @ ensures true; //NOSONAR
      @*/
    public Lezione() {}

    /**
     * Costruttore con parametri.
     *
     * @param oraInizio L'orario di inizio.
     * @param semestre Il semestre considerato.
     * @param oraFine L'orario di fine.
     * @param giorno Il giorno della settimana,.
     * @param resto Informazioni aggiuntive sulla lezione.
     * @param corso Il corso associato.
     * @param aula L'aula della lezione
     * */
    /*@
      @ public normal_behavior
      @ assignable \everything; //NOSONAR
      @ ensures this.semestre == semestre; //NOSONAR
      @ ensures this.oraInizio == oraInizio; //NOSONAR
      @ ensures this.oraFine == oraFine; //NOSONAR
      @ ensures this.giorno == giorno; //NOSONAR
      @ ensures this.resto == resto; //NOSONAR
      @ ensures this.corso == corso; //NOSONAR
      @ ensures this.aula == aula; //NOSONAR
      @ ensures true; //NOSONAR
      @*/
    public Lezione(int semestre, Time oraInizio, Time oraFine, Giorno giorno, Resto resto, Corso corso, Aula aula) {
        this.oraInizio = oraInizio;
        this.semestre = semestre;
        this.oraFine = oraFine;
        this.giorno = giorno;
        this.resto = resto;
        this.corso = corso;
        this.aula = aula;
    }

    /**
     * Ottiene la lista di docenti associati alla lezione.
     *
     * @return Lista di docenti.
     */
    /*@
      @ public normal_behavior
      @ assignable \nothing; //NOSONAR
      @ ensures \result == docenti; //NOSONAR
      @*/
    public /*@ nullable */ List<Docente> getDocenti() {
        return docenti;
    }

    /**
     * Imposta la lista di docenti associati alla lezione.
     *
     * @param docenti Lista di docenti.
     */
    /*@
      @ public normal_behavior
      @ assignable this.docenti; //NOSONAR
      @ ensures this.docenti == docenti; //NOSONAR
      @*/
    public void setDocenti(List<Docente> docenti) {
        this.docenti = docenti;
    }

    /**
     * Ottiene il semestre in cui è presente della lezione.
     *
     * @return semestre della lezione
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing; //NOSONAR
      @ ensures \result == semestre; //NOSONAR
      @*/
    public int getSemestre() {
        return semestre;
    }

    /**Imposta il semestre in cui è presente la lezione.
     *
     * @param semestre Semestre in cui è presente la lezione.
     * */
    /*@
      @ public normal_behavior
      @ assignable this.semestre; //NOSONAR
      @ ensures this.semestre == semestre; //NOSONAR
      @*/
    public void setSemestre(int semestre) {
        this.semestre = semestre;
    }

    /**
     * Ottiene l'ora di inizio della lezione.
     *
     * @return ora dell'inizio della lezione
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing; //NOSONAR
      @ ensures \result == oraInizio; //NOSONAR
     */
    public /*@ nullable */ Time getOraInizio() {
        return oraInizio;
    }

    /**Imposta l'ora di inizio della lezione.
     *
     * @param oraInizio L'ora di inzio della lezione.
     * */
    /*@
      @ public normal_behavior
      @ assignable this.oraInizio; //NOSONAR
      @ ensures this.oraInizio == oraInizio; //NOSONAR
     */
    public void setOraInizio(Time oraInizio) {
        this.oraInizio = oraInizio;
    }

    /**
     * Ottiene l'ora di fine della lezione.
     *
     * @return ora di fine della lezione
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing; //NOSONAR
      @ ensures \result == oraFine; //NOSONAR
     */
    public /*@ nullable */ Time getOraFine() {
        return oraFine;
    }

    /**Imposta l'ora di fine della lezione.
     *
     * @param oraFine L'ora di inzio della lezione.
     * */
    /*@
      @ public normal_behavior
      @ assignable this.oraFine; //NOSONAR
      @ ensures this.oraFine == oraFine; //NOSONAR
     */
    public void setOraFine(Time oraFine) {
        this.oraFine = oraFine;
    }

    /**
     * Ottiene il giorno della lezione.
     *
     * @return giorno della lezione
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing; //NOSONAR
      @ ensures \result == giorno; //NOSONAR
      @*/
    public /*@ nullable */ Giorno getGiorno() {
        return giorno;
    }

    /**Imposta il giorno della lezione.
     *
     * @param giorno Giorno della lezione.
     * */
    /*@
      @ public normal_behavior
      @ assignable this.giorno; //NOSONAR
      @ ensures this.giorno == giorno; //NOSONAR
      @*/
    public void setGiorno(Giorno giorno) {
        this.giorno = giorno;
    }

    /**
     * Ottiene il resto in cui è presente la lezione.
     *
     * @return resto in cui è presente la lezione
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing; //NOSONAR
      @ ensures \result == resto; //NOSONAR
      @*/
    public /*@ nullable */ Resto getResto() {
        return resto;
    }

    /**Imposta il resto in cui è presente la lezione.
     *
     * @param resto Resto in cui è presente la lezione.
     * */
    /*@
      @ public normal_behavior
      @ assignable this.resto; //NOSONAR
      @ ensures this.resto == resto; //NOSONAR
      @*/
    public void setResto(Resto resto) {
        this.resto = resto;
    }

    /**
     * Ottiene l'id della lezione.
     *
     * @return id della lezione
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing; //NOSONAR
      @ ensures \result == id; //NOSONAR
      @*/
    public /*@ nullable */ Long getId() {
        return id;
    }

    /**
     * Ottiene il corso in cui è presente la lezione.
     *
     * @return il corso in cui è presente la lezione
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing; //NOSONAR
      @ ensures \result == corso; //NOSONAR
      @*/
    public /*@ nullable */ Corso getCorso() {
        return corso;
    }

    /**
     * Ottiene l'aula della lezione.
     *
     * @return aula della lezione
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing; //NOSONAR
      @ ensures \result == aula; //NOSONAR
     */
    public /*@ nullable */ Aula getAula() {
        return aula;
    }

    /**Imposta l'aula in cui è presente la lezione.
     *
     * @param aula Aula in cui è presente la lezione.
     * */
    /*@
      @ public normal_behavior
      @ assignable this.aula; //NOSONAR
      @ ensures this.aula == aula; //NOSONAR
      @*/
    public void setAula(Aula aula) {
        this.aula = aula;
    }

    /**Imposta il corso in cui è presente la lezione.
     *
     * @param corso Corso in cui è presente la lezione.
     * */
    /*@
      @ public normal_behavior
      @ assignable this.corso; //NOSONAR
      @ ensures this.corso == corso; //NOSONAR
      @*/
    public void setCorso(Corso corso) {
        this.corso = corso;
    }

    /**
     * Restituisce una rappresentazione testuale dell'oggetto.
     *
     * @return Stringa rappresentativa della lezione.
     * */
    //@ skipesc
    @Override
    public String toString() {
        return "Lezione{" +
                "id=" + id +
                ", semestre=" + semestre +
                ", oraInizio=" + oraInizio +
                ", oraFine=" + oraFine +
                ", giorno=" + giorno +
                ", corso=" + corso +
                ", resto=" + resto +
                ", aula=" + aula +
                '}';
    }
}