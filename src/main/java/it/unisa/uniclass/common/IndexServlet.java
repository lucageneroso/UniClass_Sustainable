package it.unisa.uniclass.common;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NameClassPair;
import javax.naming.NamingEnumeration;
import java.io.IOException;
import java.util.List;

@WebServlet("/Home")
public class IndexServlet extends HttpServlet {

    private static final Logger LOGGER =
            LoggerFactory.getLogger(IndexServlet.class);

    private void listJNDI(final Context ctx, final String name) throws Exception {
        final NamingEnumeration<NameClassPair> list = ctx.list(name);

        while (list.hasMore()) {
            final NameClassPair nc = list.next();
            final String fullName =
                    name + (name.endsWith("/") ? "" : "/") + nc.getName();

            LOGGER.info("JNDI Name: {}", fullName);

            try {
                listJNDI(ctx, fullName);
            } catch (final Exception e) {
                // not a subcontext, ignore
            }
        }
    }

    @Override
    protected void doGet(
            final HttpServletRequest request,
            final HttpServletResponse response)
            throws ServletException, IOException {

        try {
            final Context ctx = new InitialContext();
            LOGGER.info("---- Listing JNDI java:global ----");
            listJNDI(ctx, "java:global");
            LOGGER.info("---- End JNDI listing ----");
        } catch ( final Exception e) {
            request.getServletContext()
                    .log("Error listing JNDI resources", e);
        }

        try {
            final CorsoLaureaService corsoLaureaService =
                    new CorsoLaureaService();

            final List<CorsoLaurea> corsi =
                    corsoLaureaService.trovaTutti();

            LOGGER.info("Corsi trovati: {}", corsi);

            request.setAttribute("corsi", corsi);
            request.getRequestDispatcher("index.jsp")
                    .forward(request, response);

        } catch (final Exception e) {
            request.getServletContext()
                    .log("Error retrieving courses", e);

            try {
                response.sendError(
                        HttpServletResponse.SC_INTERNAL_SERVER_ERROR,
                        "An error occurred processing your request"
                );
            } catch (final IOException ioException) {
                request.getServletContext()
                        .log("Failed to send error response", ioException);
            }
        }
    }
}
