package it.unisa.uniclass.orari.controller;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import it.unisa.uniclass.orari.service.RestoService;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.json.JSONArray;
import org.json.JSONObject;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.List;

@WebServlet(name = "getResto", value = "/getResto")
public class getResto extends HttpServlet {

    @Override
    protected void doGet(final HttpServletRequest request, final HttpServletResponse response) {
        try {
            final PrintWriter printWriter = response.getWriter();

            final String corsoLaurea = request.getParameter("corsoLaurea");
            final CorsoLaureaService corsoLaureaService = new CorsoLaureaService();
            final CorsoLaurea corsoL = corsoLaureaService.trovaCorsoLaurea(corsoLaurea);

            final JSONArray jsonArray = new JSONArray();

            final RestoService restoService = new RestoService();

            final List<Resto> resti = restoService.trovaRestiCorsoLaurea(corsoL);


            for(final Resto resto : resti) {
                final JSONObject restoJson = new JSONObject();
                restoJson.put("id", resto.getId());
                restoJson.put("nome", resto.getNome());
                jsonArray.put(restoJson);
            }


            response.setContentType("application/json");
            response.setCharacterEncoding("UTF-8");

            printWriter.println(jsonArray.toString());
            printWriter.flush();
        } catch (final Exception e) {
            request.getServletContext().log("Error processing getResto request", e);
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