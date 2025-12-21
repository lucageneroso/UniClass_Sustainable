package it.unisa.uniclass.orari.controller;

import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.orari.service.AnnoDidatticoService;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import it.unisa.uniclass.orari.service.LezioneService;
import it.unisa.uniclass.orari.service.RestoService;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;
import java.util.Comparator;
import java.util.List;

@WebServlet(name = "cercaOrarioServlet", value = "/cercaOrario")
public class cercaOrario extends HttpServlet {

    @Override
    protected void doPost(final HttpServletRequest request, final HttpServletResponse response) {
        try {
            final String corsoNome = request.getParameter("corsoLaurea");
            final String restoNome = request.getParameter("resto");
            final String annoNome = request.getParameter("anno");

            final CorsoLaureaService corsoLaureaService = new CorsoLaureaService();
            final CorsoLaurea corsoLaurea = corsoLaureaService.trovaCorsoLaurea(corsoNome);


            //Prendo il resto
            final RestoService restoService = new RestoService();
            final Resto resto = restoService.trovaRestoNomeCorso(restoNome, corsoLaurea);

            //Prendo l'anno di quel certo corso (e l'anno ha un certo nome)
            final AnnoDidatticoService annoDidatticoService = new AnnoDidatticoService();
            final AnnoDidattico annoDidattico = annoDidatticoService.trovaTuttiCorsoLaureaNome(corsoLaurea.getId(),annoNome);

            //Prendo le lezioni di quel corsoLaurea, quel resto e quell'anno
            final LezioneService lezioneService = new LezioneService();
            final List<Lezione> lezioni = lezioneService.trovaLezioniCorsoLaureaRestoAnno(corsoLaurea.getId(),resto.getId(),annoDidattico.getId());

            lezioni.sort(Comparator.comparing(Lezione::getGiorno).thenComparing(Lezione::getOraInizio));


            request.setAttribute("lezioni", lezioni);
            request.setAttribute("corsoLaurea", corsoLaurea);
            request.setAttribute("resto", resto);
            request.setAttribute("anno", annoDidattico);

            request.getRequestDispatcher("/OrarioSingolo.jsp").forward(request, response);
        } catch (final Exception e) {
            request.getServletContext().log("Error processing orario request", e);
            try {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (final IOException ioException) {
                request.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }

    @Override
    protected void doGet(final HttpServletRequest request, final HttpServletResponse response) {
        doPost(request, response);
    }

}
