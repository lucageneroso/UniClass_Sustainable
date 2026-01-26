package it.unisa.uniclass.testing.unit.common.filter;

import it.unisa.uniclass.common.Filter.HomeRedirectFilter;
import jakarta.servlet.FilterChain;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.mockito.Mockito.*;

class HomeRedirectFilterTest {

    private HomeRedirectFilter filter;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private FilterChain chain;

    @BeforeEach
    void setUp() {
        filter = new HomeRedirectFilter();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        chain = mock(FilterChain.class);
    }

    @Test
    void testDoFilterRedirectsToHome() throws IOException, ServletException {
        when(request.getContextPath()).thenReturn("/UniClass");

        filter.doFilter(request, response, chain);

        verify(response).sendRedirect("/UniClass/Home");
        // Verifichiamo che il chain non venga mai chiamato, confermando il redirect
        verify(chain, never()).doFilter(request, response);
    }

    // Il test testInitAndDestroy è stato rimosso poiché i metodi sono stati
    // eliminati dalla classe implementation in ottica di sostenibilità (codice ridondante).
}