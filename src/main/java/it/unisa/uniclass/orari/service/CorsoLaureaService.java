package it.unisa.uniclass.orari.service;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.dao.CorsoLaureaRemote;
import jakarta.ejb.Stateless;
import jakarta.persistence.NoResultException;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import java.util.List;

/**
 * Classe di servizio per la gestione delle operazioni relative ai corsi di laurea.
 * Fornisce metodi per recuperare, aggiungere e rimuovere corsi di laurea.
 */
@Stateless
public class CorsoLaureaService {

    private final CorsoLaureaRemote corsoLaureaDAO;

    /**
     * Costruttore di default che esegue il lookup JNDI del DAO.
     */
    public CorsoLaureaService() {
        try {
            final InitialContext ctx = new InitialContext();
            this.corsoLaureaDAO = (CorsoLaureaRemote) ctx.lookup("java:global/UniClass-Dependability/CorsoLaureaDAO!it.unisa.uniclass.orari.service.dao.CorsoLaureaRemote");
        } catch (final NamingException e) {
            throw new RuntimeException("Errore durante il lookup di CorsoLaureaDAO.", e);
        }
    }

    /**
     * Costruttore per uso interno e test.
     * Permette l'iniezione diretta del DAO senza lookup JNDI.
     * @param corsoLaureaDAO il DAO da usare
     */
    public CorsoLaureaService(CorsoLaureaRemote corsoLaureaDAO) {
        this.corsoLaureaDAO = corsoLaureaDAO;
    }

    /**
     * Trova un corso di laurea nel database utilizzando il suo ID.
     *
     * @param id L'ID del corso di laurea da cercare.
     * @return L'oggetto CorsoLaurea corrispondente all'ID.
     */
    public CorsoLaurea trovaCorsoLaurea(final long id) {
        try {
            return corsoLaureaDAO.trovaCorsoLaurea(id);
        } catch (final NoResultException e) {
            return null;
        }
    }

    /**
     * Trova un corso di laurea nel database utilizzando il suo nome.
     *
     * @param nome Il nome del corso di laurea da cercare.
     * @return L'oggetto CorsoLaurea corrispondente al nome.
     */
    public CorsoLaurea trovaCorsoLaurea(final String nome) {
        try {
            return corsoLaureaDAO.trovaCorsoLaurea(nome);
        } catch (final NoResultException e) {
            return null;
        }
    }

    /**
     * Recupera tutti i corsi di laurea presenti nel database.
     *
     * @return Una lista di tutti i corsi di laurea.
     */
    public List<CorsoLaurea> trovaTutti() {
        try {
            return corsoLaureaDAO.trovaTutti();
        } catch (final Exception e) {
            throw new RuntimeException("Errore durante il recupero dei corsi di laurea.", e);
        }
    }

    /**
     * Aggiunge o aggiorna un corso di laurea nel database.
     *
     * @param corsoLaurea Il corso di laurea da aggiungere o aggiornare.
     * @throws IllegalArgumentException Se il corso di laurea è null o non ha un nome valido.
     */
    public void aggiungiCorsoLaurea(final CorsoLaurea corsoLaurea) {
        if (corsoLaurea == null || corsoLaurea.getNome() == null || corsoLaurea.getNome().isEmpty()) {
            throw new IllegalArgumentException("Il corso di laurea deve avere un nome valido.");
        }
        corsoLaureaDAO.aggiungiCorsoLaurea(corsoLaurea);
    }

    /**
     * Rimuove un corso di laurea dal database.
     *
     * @param corsoLaurea Il corso di laurea da rimuovere.
     * @throws IllegalArgumentException Se il corso di laurea è null.
     */
    public void rimuoviCorsoLaurea(final CorsoLaurea corsoLaurea) {
        if (corsoLaurea == null) {
            throw new IllegalArgumentException("Il corso di laurea da rimuovere non può essere null.");
        }
        corsoLaureaDAO.rimuoviCorsoLaurea(corsoLaurea);
    }
}