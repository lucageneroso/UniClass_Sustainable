package it.unisa.uniclass.common.Filter;

import jakarta.servlet.*;
import jakarta.servlet.annotation.WebFilter;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;

@WebFilter("/index.jsp")
public class HomeRedirectFilter implements Filter {

    @Override
    // Aggiunto 'final' al parametro
    public void init(final FilterConfig filterConfig) throws ServletException {
        Filter.super.init(filterConfig);
    }

    @Override
    // Aggiunto 'final' ai parametri e alle variabili locali
    public void doFilter(final ServletRequest servletRequest, final ServletResponse servletResponse, final FilterChain filterChain) throws IOException, ServletException {
        final HttpServletRequest httpRequest = (HttpServletRequest) servletRequest;
        final HttpServletResponse httpResponse = (HttpServletResponse) servletResponse;

        httpResponse.sendRedirect(httpRequest.getContextPath() + "/Home");
        // return; -> Rimosso perché ridondante (Code Smell java:S1128)
    }

    @Override
    public void destroy() {
        Filter.super.destroy();
    }
}