package it.unisa.uniclass.orari.controller;

import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.AnnoDidatticoService;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.json.JSONArray;
import org.json.JSONObject;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.List;


@WebServlet(name = "getAnno", value = "/getAnno")
public class getAnno extends HttpServlet {

    @Override
    protected void doGet(final HttpServletRequest request, final HttpServletResponse response) {
        try {
            final PrintWriter printWriter = response.getWriter();

            final String corsoLaurea = request.getParameter("corsoLaurea");
            final CorsoLaureaService corsoLaureaService = new CorsoLaureaService();
            final CorsoLaurea corsoL = corsoLaureaService.trovaCorsoLaurea(corsoLaurea);

            final JSONArray jsonArray = new JSONArray();

            final AnnoDidatticoService annoDidatticoService = new AnnoDidatticoService();


            final List<AnnoDidattico> anni = annoDidatticoService.trovaTuttiCorsoLaurea(corsoL.getId());


            for (final AnnoDidattico anno : anni) {
                final JSONObject annoJson = new JSONObject();
                annoJson.put("id", anno.getId());
                annoJson.put("nome", anno.getAnno());
                jsonArray.put(annoJson);
            }

            response.setContentType("application/json");
            response.setCharacterEncoding("UTF-8");

            printWriter.println(jsonArray.toString());
            printWriter.flush();
        } catch (final Exception e) {
            request.getServletContext().log("Error processing getAnno request", e);
            try {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (final IOException ioException) {
                request.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }
    @Override
    protected void doPost(final HttpServletRequest request, final HttpServletResponse response) {
        doGet(request, response);
    }

}