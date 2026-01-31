package it.unisa.uniclass.common.filter;

import jakarta.servlet.*;
import jakarta.servlet.annotation.WebFilter;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * Filtro per Rate Limiting - previene attacchi DDoS e brute-force.
 * Limita il numero di richieste per IP in una finestra temporale.
 */
@WebFilter(urlPatterns = "/*", filterName = "RateLimitFilter")
public class RateLimitFilter implements Filter {

    // Configurazione
    private static final int MAX_REQUESTS_PER_MINUTE = 100;  // Richieste max per minuto
    private static final int MAX_LOGIN_ATTEMPTS_PER_MINUTE = 5;  // Tentativi login max
    private static final long WINDOW_MS = 60_000;  // 1 minuto

    // Storage per conteggio richieste (IP -> RequestCount)
    private final ConcurrentHashMap<String, RequestTracker> requestCounts = new ConcurrentHashMap<>();

    @Override
    public void init(FilterConfig filterConfig) throws ServletException {
        // Pulizia periodica ogni 5 minuti (in produzione usare ScheduledExecutor)
    }

    @Override
    public void doFilter(ServletRequest request, ServletResponse response, FilterChain chain)
            throws IOException, ServletException {

        HttpServletRequest httpRequest = (HttpServletRequest) request;
        HttpServletResponse httpResponse = (HttpServletResponse) response;

        String clientIP = getClientIP(httpRequest);
        String path = httpRequest.getRequestURI();

        // Determina il limite in base all'endpoint
        int limit = path.contains("/Login") ? MAX_LOGIN_ATTEMPTS_PER_MINUTE : MAX_REQUESTS_PER_MINUTE;

        RequestTracker tracker = requestCounts.computeIfAbsent(clientIP, k -> new RequestTracker());

        if (tracker.isRateLimited(limit)) {
            httpResponse.setStatus(429);  // Too Many Requests
            httpResponse.setHeader("Retry-After", "60");
            httpResponse.getWriter().write("Troppe richieste. Riprova tra un minuto.");
            return;
        }

        tracker.increment();
        chain.doFilter(request, response);
    }

    @Override
    public void destroy() {
        requestCounts.clear();
    }

    private String getClientIP(HttpServletRequest request) {
        String xForwardedFor = request.getHeader("X-Forwarded-For");
        if (xForwardedFor != null && !xForwardedFor.isEmpty()) {
            return xForwardedFor.split(",")[0].trim();
        }
        return request.getRemoteAddr();
    }

    /**
     * Tracker per singolo IP con finestra temporale sliding.
     */
    private static class RequestTracker {
        private final AtomicInteger count = new AtomicInteger(0);
        private volatile long windowStart = System.currentTimeMillis();

        public synchronized boolean isRateLimited(int limit) {
            long now = System.currentTimeMillis();
            if (now - windowStart > WINDOW_MS) {
                // Reset finestra
                count.set(0);
                windowStart = now;
            }
            return count.get() >= limit;
        }

        public void increment() {
            count.incrementAndGet();
        }
    }
}
