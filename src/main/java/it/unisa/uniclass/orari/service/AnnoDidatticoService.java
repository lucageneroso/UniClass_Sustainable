package it.unisa.uniclass.orari.service;

import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.service.dao.AnnoDidatticoRemote;
import jakarta.ejb.Stateless;
import jakarta.persistence.NoResultException;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import java.util.List;

/**
 * Classe di servizio per la gestione delle operazioni relative agli anni didattici.
 * Fornisce metodi per recuperare, aggiungere e rimuovere anni didattici.
 */
@Stateless
public class AnnoDidatticoService {

    public final AnnoDidatticoRemote annoDidatticoDao;

    /**
     * Costruttore di default che esegue il lookup JNDI del DAO.
     */
    public AnnoDidatticoService() {
        try {
            final InitialContext ctx = new InitialContext();
            this.annoDidatticoDao = (AnnoDidatticoRemote) ctx.lookup("java:global/UniClass-Dependability/AnnoDidatticoDAO");
        } catch (final NamingException e) {
            throw new RuntimeException("Errore durante il lookup di AnnoDidatticoDAO.", e);
        }
    }

    /**
     * Costruttore per uso interno e test.
     * Permette l'iniezione diretta del DAO senza lookup JNDI.
     * @param annoDidatticoDao il DAO da usare
     */
    public AnnoDidatticoService(AnnoDidatticoRemote annoDidatticoDao) {
        this.annoDidatticoDao = annoDidatticoDao;
    }

    /**
     * Trova gli anni didattici nel database utilizzando l'anno.
     *
     * @param anno L'anno didattico da cercare.
     * @return Una lista di oggetti AnnoDidattico corrispondenti all'anno.
     */
    public List<AnnoDidattico> trovaAnno(final String anno) {
        return annoDidatticoDao.trovaAnno(anno);
    }

    /**
     * Trova un anno didattico nel database utilizzando il suo ID.
     *
     * @param id L'ID dell'anno didattico da cercare.
     * @return L'oggetto AnnoDidattico corrispondente all'ID.
     */
    public AnnoDidattico trovaId(final int id) {
        try {
            return annoDidatticoDao.trovaId(id);
        } catch (final NoResultException e) {
            return null;
        }
    }

    /**
     * Recupera tutti gli anni didattici presenti nel database.
     *
     * @return Una lista di tutti gli anni didattici.
     */
    public List<AnnoDidattico> trovaTutti() {
        return annoDidatticoDao.trovaTutti();
    }

    /**
     * Aggiunge o aggiorna un anno didattico nel database.
     *
     * @param annoDidattico L'anno didattico da aggiungere o aggiornare.
     */
    public void aggiungiAnno(final AnnoDidattico annoDidattico) {
        annoDidatticoDao.aggiungiAnno(annoDidattico);
    }

    /**
     * Rimuove un anno didattico dal database.
     *
     * @param annoDidattico L'anno didattico da rimuovere.
     */
    public void rimuoviAnno(final AnnoDidattico annoDidattico) {
        annoDidatticoDao.rimuoviAnno(annoDidattico);
    }

    /**
     * Trova tutti gli anni didattici nel database associati a un corso di laurea tramite l'ID del corso.
     *
     * @param id L'ID del corso di laurea di cui trovare gli anni didattici.
     * @return Una lista di oggetti AnnoDidattico associati al corso di laurea.
     */
    public List<AnnoDidattico> trovaTuttiCorsoLaurea(final long id) {
        return annoDidatticoDao.trovaTuttiCorsoLaurea(id);
    }

    /**
     * Trova un anno didattico nel database associato a un corso di laurea tramite l'ID del corso e l'anno.
     *
     * @param id L'ID del corso di laurea.
     * @param anno L'anno didattico da cercare.
     * @return L'oggetto AnnoDidattico corrispondente all'ID del corso e all'anno.
     */
    public AnnoDidattico trovaTuttiCorsoLaureaNome(final long id, final String anno) {
        try {
            return annoDidatticoDao.trovaCorsoLaureaNome(id, anno);
        } catch (final NoResultException e) {
            return null;
        }
    }
}