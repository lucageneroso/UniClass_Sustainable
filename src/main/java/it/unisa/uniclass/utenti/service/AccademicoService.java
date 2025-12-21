package it.unisa.uniclass.utenti.service;

import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.service.dao.AccademicoRemote;
import jakarta.ejb.Stateless;
import jakarta.persistence.NoResultException;

import javax.naming.InitialContext;
import javax.naming.NamingException;
import java.util.List;

/**
 * Classe di servizio per la gestione delle operazioni relative agli accademici.
 * Fornisce metodi per recuperare, aggiungere e rimuovere accademici.
 */
@Stateless
public class AccademicoService {

    private final AccademicoRemote accademicoDao;

    /**
     * Costruttore di default che esegue il lookup JNDI del DAO.
     */
    public AccademicoService() {
        try {
            System.out.println(" ATTENZIONE: Sto facendo la lookup JNDI del DAO! ");
            final InitialContext ctx = new InitialContext();
            accademicoDao = (AccademicoRemote) ctx.lookup("java:global/UniClass-Dependability/AccademicoDAO");
        } catch (final NamingException e) {
            throw new RuntimeException("Errore durante il lookup di AccademicoDAO", e);
        }
    }
    
    /**
     * Costruttore per i Test.
     * @param dao Il DAO mockato.
     */
    public AccademicoService(AccademicoRemote dao){
        this.accademicoDao = dao;
    }
    

    /**
     * Trova un accademico nel database utilizzando la sua matricola.
     *
     * @param matricola La matricola dell'accademico da cercare.
     * @return L'oggetto Accademico corrispondente alla matricola.
     */
    public Accademico trovaAccademicoUniClass(final String matricola) {
        try {
            return accademicoDao.trovaAccademicoUniClass(matricola);
        } catch (final NoResultException e) {
            return null;
        }
    }

    /**
     * Trova un accademico nel database utilizzando la sua email e password.
     *
     * @param email L'email dell'accademico da cercare.
     * @param pass La password dell'accademico da cercare.
     * @return L'oggetto Accademico corrispondente all'email e alla password.
     */
    public Accademico trovaEmailPassUniclass(final String email, final String pass) {
        try {
            final Accademico accademico = accademicoDao.trovaEmailUniClass(email);
            if (accademico != null) {
                if (accademico.getPassword() == null || accademico.getPassword().equals(pass)) {
                    return accademico;
                } else {
                    return null;
                }
            } else {
                return null;
            }
        } catch (final NoResultException e) {
            return null;
        }
    }

    /**
     * Recupera tutti gli accademici presenti nel database.
     *
     * @return Una lista di tutti gli accademici.
     */
    public List<Accademico> trovaTuttiUniClass() {
        return accademicoDao.trovaTuttiUniClass();
    }

    /**
     * Trova un accademico nel database utilizzando la sua email.
     *
     * @param email L'email dell'accademico da cercare.
     * @return L'oggetto Accademico corrispondente all'email.
     */
    public Accademico trovaEmailUniClass(final String email) {
        try {
            return accademicoDao.trovaEmailUniClass(email);
        } catch (final NoResultException e) {
            return null;
        }
    }

    /**
     * Trova gli accademici nel database che sono attivati o disattivati.
     *
     * @param attivato Lo stato di attivazione degli accademici da cercare.
     * @return Una lista di oggetti Accademico corrispondenti allo stato di attivazione.
     */
    public List<Accademico> trovaAttivati(final boolean attivato) {
        return accademicoDao.trovaAttivati(attivato);
    }

    /**
     * Aggiunge o aggiorna un accademico nel database.
     *
     * @param accademico L'accademico da aggiungere o aggiornare.
     */
    public void aggiungiAccademico(final Accademico accademico) {
        accademicoDao.aggiungiAccademico(accademico);
    }

    /**
     * Rimuove un accademico dal database.
     *
     * @param accademico L'accademico da rimuovere.
     */
    public void rimuoviAccademico(final Accademico accademico) {
        accademicoDao.rimuoviAccademico(accademico);
    }

    /**
     * Recupera tutte le email degli accademici presenti nel database.
     *
     * @return Una lista di email degli accademici.
     */
    public List<String> retrieveEmail() {
        return accademicoDao.retrieveEmail();
    }

    /**
     * Cambia lo stato di attivazione di un accademico nel database.
     *
     * @param accademico L'accademico di cui cambiare lo stato di attivazione.
     * @param attivazione Il nuovo stato di attivazione.
     */
    public void cambiaAttivazione(final Accademico accademico, final boolean attivazione) {
        accademicoDao.cambiaAttivazione(accademico, attivazione);
    }
}
