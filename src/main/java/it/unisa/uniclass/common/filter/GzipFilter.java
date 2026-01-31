package it.unisa.uniclass.common.filter;

import jakarta.servlet.*;
import jakarta.servlet.annotation.WebFilter;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpServletResponseWrapper;

import java.io.*;
import java.util.zip.GZIPOutputStream;

/**
 * Filtro per compressione GZIP delle risposte.
 * Riduce la dimensione delle risposte del 60-80%.
 */
@WebFilter(urlPatterns = "/*", filterName = "GzipFilter")
public class GzipFilter implements Filter {

    @Override
    public void init(FilterConfig filterConfig) throws ServletException {
    }

    @Override
    public void doFilter(ServletRequest request, ServletResponse response, FilterChain chain)
            throws IOException, ServletException {

        HttpServletRequest httpRequest = (HttpServletRequest) request;
        HttpServletResponse httpResponse = (HttpServletResponse) response;

        String acceptEncoding = httpRequest.getHeader("Accept-Encoding");
        String uri = httpRequest.getRequestURI();

        // Comprimi solo se il client supporta GZIP e non è già un file binario
        if (acceptEncoding != null && acceptEncoding.contains("gzip") && isCompressible(uri)) {
            GzipResponseWrapper gzipResponse = new GzipResponseWrapper(httpResponse);
            try {
                chain.doFilter(request, gzipResponse);
                gzipResponse.finish();
            } catch (Exception e) {
                // Fallback senza compressione in caso di errore
                chain.doFilter(request, response);
            }
        } else {
            chain.doFilter(request, response);
        }
    }

    @Override
    public void destroy() {
    }

    private boolean isCompressible(String uri) {
        // Non comprimere file già compressi
        String lower = uri.toLowerCase();
        return !lower.endsWith(".gz") &&
               !lower.endsWith(".zip") &&
               !lower.endsWith(".png") &&
               !lower.endsWith(".jpg") &&
               !lower.endsWith(".jpeg") &&
               !lower.endsWith(".gif") &&
               !lower.endsWith(".ico");
    }

    /**
     * Wrapper per risposta GZIP.
     */
    private static class GzipResponseWrapper extends HttpServletResponseWrapper {
        private GzipServletOutputStream gzipOutputStream;
        private PrintWriter printWriter;

        public GzipResponseWrapper(HttpServletResponse response) {
            super(response);
            response.addHeader("Content-Encoding", "gzip");
            response.addHeader("Vary", "Accept-Encoding");
        }

        @Override
        public ServletOutputStream getOutputStream() throws IOException {
            if (gzipOutputStream == null) {
                gzipOutputStream = new GzipServletOutputStream(getResponse().getOutputStream());
            }
            return gzipOutputStream;
        }

        @Override
        public PrintWriter getWriter() throws IOException {
            if (printWriter == null) {
                printWriter = new PrintWriter(new OutputStreamWriter(getOutputStream(), getCharacterEncoding()));
            }
            return printWriter;
        }

        public void finish() throws IOException {
            if (printWriter != null) {
                printWriter.close();
            }
            if (gzipOutputStream != null) {
                gzipOutputStream.finish();
            }
        }
    }

    /**
     * OutputStream con compressione GZIP.
     */
    private static class GzipServletOutputStream extends ServletOutputStream {
        private final GZIPOutputStream gzipStream;

        public GzipServletOutputStream(OutputStream output) throws IOException {
            this.gzipStream = new GZIPOutputStream(output);
        }

        @Override
        public void write(int b) throws IOException {
            gzipStream.write(b);
        }

        @Override
        public void write(byte[] b, int off, int len) throws IOException {
            gzipStream.write(b, off, len);
        }

        public void finish() throws IOException {
            gzipStream.finish();
        }

        @Override
        public boolean isReady() {
            return true;
        }

        @Override
        public void setWriteListener(WriteListener listener) {
        }
    }
}
