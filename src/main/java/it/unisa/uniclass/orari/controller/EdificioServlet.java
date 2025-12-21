package it.unisa.uniclass.orari.controller;

import it.unisa.uniclass.orari.model.Aula;
import it.unisa.uniclass.orari.service.AulaService;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import javax.naming.NamingException;
import java.io.IOException;
import java.util.List;

@WebServlet(name = "EdificioServlet", value = "/EdificioServlet")
public class EdificioServlet extends HttpServlet {

    @Override
    protected void doGet(final HttpServletRequest req, final HttpServletResponse resp) {
        try {
            final String edificio = req.getParameter("ed");

            AulaService aulaService = null;
            try {
                aulaService = new AulaService();
            } catch (final NamingException e) {
                req.getServletContext().log("Error creating AulaService", e);
                resp.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
                return;
            }

            final List<Aula> aule = aulaService.trovaAuleEdificio(edificio);

            req.setAttribute("aule", aule);
            req.setAttribute("ed", edificio);
            req.getRequestDispatcher("/edificio.jsp").forward(req, resp);
        } catch (final Exception e) {
            req.getServletContext().log("Error processing edificio request", e);
            try {
                resp.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (final IOException ioException) {
                req.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }

    @Override
    protected void doPost(final HttpServletRequest req, final HttpServletResponse resp) {
        doGet(req, resp);
    }
}
