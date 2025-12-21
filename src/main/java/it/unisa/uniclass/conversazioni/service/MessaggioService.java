package it.unisa.uniclass.conversazioni.service;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.dao.MessaggioRemote;
import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.ejb.Stateless;
import jakarta.persistence.NoResultException;

import javax.naming.InitialContext;
import javax.naming.NamingException;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

/**
 * Classe di servizio per la gestione delle operazioni relative ai messaggi.
 */
@Stateless
public class MessaggioService {

    /**
     * Eccezione specifica per errori di inizializzazione del servizio.
     */
    public static class MessaggioServiceInitializationException extends RuntimeException {
        public MessaggioServiceInitializationException(final String message, final Throwable cause) {
            super(message, cause);
        }
    }

    private final MessaggioRemote messaggioDao;

    /**
     * Costruttore di default che esegue il lookup JNDI del DAO.
     */
    public MessaggioService() {
        try {
            final InitialContext ctx = new InitialContext();
            messaggioDao = (MessaggioRemote) ctx.lookup("java:global/UniClass-Dependability/MessaggioDAO");
        } catch (final NamingException e) {
            throw new MessaggioServiceInitializationException(
                    "Impossibile trovare il MessaggioDAO tramite JNDI", e
            );
        }
    }

    public Messaggio trovaMessaggio(final long id) {
        try {
            return messaggioDao.trovaMessaggio(id);
        } catch (final NoResultException e) {
            return null;
        }
    }

    public List<Messaggio> trovaMessaggiInviati(final String matricola) {
        return messaggioDao.trovaMessaggiInviati(matricola);
    }

    public List<Messaggio> trovaMessaggiRicevuti(final String matricola) {
        return messaggioDao.trovaMessaggiRicevuti(matricola);
    }

    public List<Messaggio> trovaMessaggi(final String matricola1,final String matricola2) {
        return messaggioDao.trovaMessaggi(matricola1, matricola2);
    }

    public List<Messaggio> trovaTutti() {
        return messaggioDao.trovaTutti();
    }

    public List<Messaggio> trovaAvvisi() {
        return messaggioDao.trovaAvvisi();
    }

    public List<Messaggio> trovaAvvisiAutore(final String autore) {
        return messaggioDao.trovaAvvisiAutore(autore);
    }

    public List<Messaggio> trovaMessaggiData(final LocalDateTime dateTime) {
        return messaggioDao.trovaMessaggiData(dateTime);
    }

    public List<Accademico> trovaMessaggeriDiUnAccademico(final String matricola) {
        final List<Messaggio> messaggi = messaggioDao.trovaMessaggiRicevuti(matricola);
        final List<Accademico> accademici = new ArrayList<>();
        for (final Messaggio messaggio : messaggi) {
            accademici.add(messaggio.getDestinatario());
        }
        return accademici;
    }

    public List<Messaggio> trovaTopic(final Topic topic) {
        return messaggioDao.trovaTopic(topic);
    }

    public Messaggio aggiungiMessaggio(Messaggio messaggio) {
        if (messaggio != null) {
            messaggio = messaggioDao.aggiungiMessaggio(messaggio);
        }
        return messaggio;
    }

    public void rimuoviMessaggio(final Messaggio messaggio) {
        if (messaggio != null) {
            messaggioDao.rimuoviMessaggio(messaggio);
        }
    }
}
