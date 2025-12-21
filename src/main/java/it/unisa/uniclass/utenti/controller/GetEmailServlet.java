package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.utenti.service.AccademicoService;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.json.JSONArray;
import org.json.JSONObject;

import java.util.List;

@WebServlet(name = "GetEmailServlet", value = "/GetEmailServlet")
public class GetEmailServlet extends HttpServlet {

    @Override
    protected void doGet(final HttpServletRequest req, final HttpServletResponse resp) {
        final AccademicoService accademicoService = new AccademicoService();

        try {
            final List<String> emails = accademicoService.retrieveEmail();

            final JSONArray jsonArray = new JSONArray(emails);

            resp.setContentType("application/json");
            resp.setCharacterEncoding("UTF-8");

            resp.getWriter().write(jsonArray.toString());
        } catch (final Exception e) {
            req.getServletContext().log("Error retrieving emails", e);

            // Gestione degli errori
            try {
                final JSONObject errorResponse = new JSONObject();
                errorResponse.put("error", "Errore durante il recupero delle email.");

                resp.setStatus(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
                resp.setContentType("application/json");
                resp.setCharacterEncoding("UTF-8");
                resp.getWriter().write(errorResponse.toString());
            } catch (final Exception innerException) {
                req.getServletContext().log("Failed to send error response", innerException);
            }
        }
    }

    @Override
    protected void doPost(final HttpServletRequest req, final HttpServletResponse resp) {
        doGet(req, resp);
    }
}
