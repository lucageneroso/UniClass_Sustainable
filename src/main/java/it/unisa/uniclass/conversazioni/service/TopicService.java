package it.unisa.uniclass.conversazioni.service;

import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.dao.TopicRemote;
import jakarta.ejb.Stateless;
import jakarta.persistence.NoResultException;

import javax.naming.InitialContext;
import javax.naming.NamingException;
import java.util.List;

/**
 * Classe di servizio per la gestione delle operazioni relative ai topic.
 * Fornisce metodi per recuperare, aggiungere e rimuovere topic.
 */
@Stateless
public class TopicService {

    /**
     * Eccezione specifica per errori di inizializzazione del TopicService.
     */
    public static class TopicServiceInitializationException extends RuntimeException {
        public TopicServiceInitializationException(final String message, final Throwable cause) {
            super(message, cause);
        }
    }

    private TopicRemote topicDao;

    /**
     * Costruttore di default che esegue il lookup JNDI del DAO.
     */
    public TopicService() {
        try {
            final InitialContext ctx = new InitialContext();
            topicDao = (TopicRemote) ctx.lookup("java:global/UniClass-Dependability/TopicDAO");
        } catch (final NamingException e) {
            throw new TopicServiceInitializationException(
                    "Impossibile trovare il TopicDAO tramite JNDI", e
            );
        }
    }

    public Topic trovaId(final long id) {
        try {
            return topicDao.trovaId(id);
        } catch (final NoResultException e) {
            return null;
        }
    }

    public Topic trovaNome(final String nome) {
        try {
            return topicDao.trovaNome(nome);
        } catch (final NoResultException e) {
            return null;
        }
    }

    public Topic trovaCorsoLaurea(final String nome) {
        try {
            return topicDao.trovaCorsoLaurea(nome);
        } catch (final NoResultException e) {
            return null;
        }
    }

    public Topic trovaCorso(final String nome) {
        try {
            return topicDao.trovaCorso(nome);
        } catch (final NoResultException e) {
            return null;
        }
    }

    public List<Topic> trovaTutti() {
        return topicDao.trovaTutti();
    }

    public void aggiungiTopic(final Topic topic) {
        topicDao.aggiungiTopic(topic);
    }

    public void rimuoviTopic(final Topic topic) {
        topicDao.rimuoviTopic(topic);
    }
}
