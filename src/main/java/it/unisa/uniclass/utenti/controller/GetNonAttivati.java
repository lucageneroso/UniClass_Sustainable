package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.service.AccademicoService;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.json.JSONArray;
import org.json.JSONObject;

import java.util.List;

@WebServlet(name = "GetNonAttivati", value = "/GetNonAttivati")
public class GetNonAttivati extends HttpServlet {

    @Override
    protected void doGet(final HttpServletRequest req, final HttpServletResponse resp) {
        try {
            final AccademicoService accademicoService = new AccademicoService();

            final List<Accademico> nonAttivati = accademicoService.trovaAttivati(false);

            final JSONArray jsonArray = new JSONArray();

            for (final Accademico accademico : nonAttivati) {
                final JSONObject jsonUtente = new JSONObject();
                jsonUtente.put("email", accademico.getEmail());
                jsonUtente.put("matricola", accademico.getMatricola());
                jsonUtente.put("tipo", accademico.getTipo());

                jsonArray.put(jsonUtente);
            }
            resp.setContentType("application/json");
            resp.setCharacterEncoding("UTF-8");

            resp.getWriter().write(jsonArray.toString());
        } catch (final Exception e) {
            req.getServletContext().log("Error processing GetNonAttivati request", e);
            try {
                resp.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (final Exception ioException) {
                req.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }

    @Override
    protected void doPost(final HttpServletRequest req, final HttpServletResponse resp) {
        doGet(req, resp);
    }
}
