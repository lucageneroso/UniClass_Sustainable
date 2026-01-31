package it.unisa.uniclass.common.filter;

import jakarta.servlet.*;
import jakarta.servlet.annotation.WebFilter;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;

/**
 * Filtro per aggiungere header di cache HTTP.
 * Migliora le performance riducendo richieste ripetute.
 */
@WebFilter(urlPatterns = {"*.css", "*.js", "*.png", "*.jpg", "*.jpeg", "*.gif", "*.ico", "*.woff", "*.woff2"},
           filterName = "CacheControlFilter")
public class CacheControlFilter implements Filter {

    // Cache risorse statiche per 1 settimana
    private static final int STATIC_CACHE_SECONDS = 604800;  // 7 giorni

    @Override
    public void init(FilterConfig filterConfig) throws ServletException {
    }

    @Override
    public void doFilter(ServletRequest request, ServletResponse response, FilterChain chain)
            throws IOException, ServletException {

        HttpServletResponse httpResponse = (HttpServletResponse) response;
        HttpServletRequest httpRequest = (HttpServletRequest) request;

        String uri = httpRequest.getRequestURI();

        // Imposta header di cache per risorse statiche
        httpResponse.setHeader("Cache-Control", "public, max-age=" + STATIC_CACHE_SECONDS);
        httpResponse.setHeader("Vary", "Accept-Encoding");

        // ETag basato sul path (semplificato)
        httpResponse.setHeader("ETag", "\"" + uri.hashCode() + "\"");

        chain.doFilter(request, response);
    }

    @Override
    public void destroy() {
    }
}
