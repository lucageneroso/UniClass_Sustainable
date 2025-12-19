package it.unisa.uniclass.testing.unit.utenti.service;

import it.unisa.uniclass.common.exceptions.AlreadyExistentUserException;
import it.unisa.uniclass.common.exceptions.NotFoundUserException;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Studente;
import it.unisa.uniclass.utenti.service.AccademicoService;
import it.unisa.uniclass.utenti.service.StudenteService;
import it.unisa.uniclass.utenti.service.dao.StudenteRemote;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.MockedConstruction;
import org.mockito.Mockito;
import org.mockito.MockitoAnnotations; // <--- Fondamentale
import jakarta.persistence.NoResultException;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import org.mockito.MockedConstruction;
import org.mockito.MockedStatic;
import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

class StudenteServiceTest {

    @Mock
    private StudenteRemote studenteDao;

    private StudenteService studenteService;

    @BeforeEach
    void setUp() {
        // Inizializzazione manuale dei Mock
        MockitoAnnotations.openMocks(this);

        // Creazione del service con il mock
        studenteService = new StudenteService(studenteDao);
    }
    @Test
    void testCostruttoreDefault() throws Exception {
        // Mock del lookup JNDI
        try (MockedConstruction<InitialContext> mockedCtx = Mockito.mockConstruction(InitialContext.class,
                (mock, context) -> {
                    when(mock.lookup("java:global/UniClass-Dependability/StudenteDAO"))
                            .thenReturn(studenteDao);
                })) {

            StudenteService service = new StudenteService(); // dovrebbe usare il mock
            assertNotNull(service); // semplice verifica che sia stato creato
        }
    }

    @Test
    void testTrovaStudenteUniClass_NoResult() {
        // Simula NoResultException lanciata dal DAO
        when(studenteDao.trovaStudenteUniClass(anyString())).thenThrow(new NoResultException());

        // Il metodo dovrebbe restituire null
        Studente s = studenteService.trovaStudenteUniClass("fantasma");
        assertNull(s);
    }

    @Test
    void testTrovaStudenteEmailUniClass_NoResult() {
        // Simula NoResultException lanciata dal DAO
        when(studenteDao.trovaStudenteEmailUniClass(anyString())).thenThrow(new NoResultException());

        // Il metodo dovrebbe restituire null
        Studente s = studenteService.trovaStudenteEmailUniClass("fantasma@unisa.it");
        assertNull(s);
    }
    @Test
    void testAggiungiStudente_Nuovo_Successo() throws Exception {
        Studente s = new Studente();
        s.setMatricola("0512100001");
        s.setEmail("s.studente@unisa.it");

        // Simula che NON esista né per email né per matricola
        when(studenteDao.trovaStudenteEmailUniClass(s.getEmail())).thenReturn(null);
        when(studenteDao.trovaStudenteUniClass(s.getMatricola())).thenReturn(null);

        studenteService.aggiungiStudente(s);

        // Verifica che venga chiamato il metodo di salvataggio
        verify(studenteDao).aggiungiStudente(s);
    }

    @Test
    void testAggiungiStudente_Esistente_LanciaEccezione() {
        Studente s = new Studente();
        s.setEmail("gia.presente@unisa.it");

        // Simula che esista già un utente con questa email
        when(studenteDao.trovaStudenteEmailUniClass(s.getEmail())).thenReturn(new Studente());

        assertThrows(AlreadyExistentUserException.class, () -> {
            studenteService.aggiungiStudente(s);
        });

        // Verifica che NON salvi nulla
        verify(studenteDao, never()).aggiungiStudente(any());
    }

    // --- COPIA QUESTO DENTRO StudenteServiceTest ---

    @Test
    void testMetodiDiRicercaSemplici() {
        // Test trova per matricola
        studenteService.trovaStudenteUniClass("123");
        verify(studenteDao).trovaStudenteUniClass("123");

        // Test trova tutti
        studenteService.trovaTuttiUniClass();
        verify(studenteDao).trovaTuttiUniClass();

        // Test trova per corso (passiamo null perché è un mock)
        studenteService.trovaStudentiCorso(null);
        verify(studenteDao).trovaStudentiCorso(null);
    }
// AGGIUNGI A StudenteServiceTest.java

    @Test
    void testRimuoviStudente_Successo_MockConstruction() throws Exception {
        Studente s = new Studente();
        s.setMatricola("0512101234");

        // 1. Il DAO Docente ci dice che lo studente esiste
        when(studenteDao.trovaStudenteUniClass(s.getMatricola())).thenReturn(s);

        // 2. MAGIC: Intercettiamo la chiamata a "new AccademicoService()"
        try (MockedConstruction<AccademicoService> mocked = Mockito.mockConstruction(AccademicoService.class,
                (mock, context) -> {
                    // Istruiamo il mock del service che verrà creato: trova un accademico associato
                    when(mock.trovaAccademicoUniClass(anyString())).thenReturn(new Accademico());
                })) {

            // Eseguiamo il metodo che contiene il "new"
            studenteService.rimuoviStudente(s);

            // Verifiche:
            verify(studenteDao).rimuoviStudente(s);

            // Verifichiamo che il service accademico (mock) sia stato chiamato per la rimozione
            verify(mocked.constructed().get(0)).rimuoviAccademico(any());

        }
    }

    @Test
    void testRimuoviStudente_NonTrovato() {
        Studente s = new Studente();
        s.setMatricola("fantasma");

        when(studenteDao.trovaStudenteUniClass(s.getMatricola())).thenReturn(null);

        assertThrows(NotFoundUserException.class, () -> {
            studenteService.rimuoviStudente(s);
        });

        // Verifica che non sia stato chiamato nessun altro DAO
        verify(studenteDao, never()).rimuoviStudente(any());
    }
    @Test
    @DisplayName("Rimuovi studente esistente - Flusso completo")
    void testRimuoviStudente_Esistente() throws Exception {
        // 1. Setup dei dati
        Studente s = new Studente();
        s.setMatricola("0512101234");
        s.setEmail("studente@example.com");

        // Simuliamo che lo studente esista nel database
        when(studenteDao.trovaStudenteUniClass(s.getMatricola())).thenReturn(s);

        // 2. Mockiamo la creazione interna di AccademicoService
        try (MockedConstruction<AccademicoService> mockedAccService = Mockito.mockConstruction(AccademicoService.class,
                (mock, context) -> {
                    // Istruiamo il mock dell'AccademicoService
                    // Quando cercherà l'account accademico associato all'email, restituiamo un oggetto non null
                    when(mock.trovaAccademicoUniClass(s.getEmail())).thenReturn(new Accademico());
                })) {

            // 3. Esecuzione del metodo sotto test
            studenteService.rimuoviStudente(s);

            // 4. ASSERTIONS

            // Verifica che il DAO abbia effettivamente rimosso lo studente
            verify(studenteDao, times(1)).rimuoviStudente(s);

            // Verifica che sia stato creato l'AccademicoService e usata l'istanza mockata
            assertFalse(mockedAccService.constructed().isEmpty(), "Dovrebbe essere stata creata un'istanza di AccademicoService");

            // Recuperiamo il mock creato internamente e verifichiamo che abbia rimosso l'accademico
            AccademicoService serviceInternoMock = mockedAccService.constructed().get(0);
            verify(serviceInternoMock, times(1)).rimuoviAccademico(any());
        }
    }
    @Test
    void testCostruttoreDefault_NamingException() {
        try (MockedConstruction<InitialContext> mockedCtx = Mockito.mockConstruction(InitialContext.class,
                (mock, context) -> {
                    when(mock.lookup("java:global/UniClass-Dependability/StudenteDAO"))
                            .thenThrow(new NamingException("Simulated JNDI error"));
                })) {

            // Quando invochi il costruttore di default, scatterà il catch
            RuntimeException ex = assertThrows(RuntimeException.class, StudenteService::new);

            assertTrue(ex.getMessage().contains("Errore durante il lookup di StudenteDAO"));
            assertTrue(ex.getCause() instanceof NamingException);
        }
    }

}