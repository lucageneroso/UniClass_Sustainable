package it.unisa.uniclass.common.security;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

/**
 * Utility class per la gestione della sicurezza delle credenziali.
 */
public final class CredentialSecurity {

    /**
     * Costruttore privato per impedire l'istanziazione.
     * La classe è una utility class e deve essere usata solo tramite metodi statici.
     */
    private CredentialSecurity() {
        // Costruttore intenzionalmente privato per nascondere quello implicito pubblico.
    }

    /**
     * Eccezione specifica per errori di hashing.
     */
    public static class PasswordHashingException extends RuntimeException {
        public PasswordHashingException(final String message, final Throwable cause) {
            super(message, cause);
        }
    }

    /**
     * Restituisce l'hash SHA-256 della password.
     *
     * @param password la password in chiaro
     * @return hash esadecimale della password
     */
    public static String hashPassword(final String password) {
        try {
            final MessageDigest digest = MessageDigest.getInstance("SHA-256");
            final byte[] hash = digest.digest(password.getBytes(StandardCharsets.UTF_8));

            final StringBuilder hexString = new StringBuilder(2 * hash.length);
            for (final byte b : hash) {
                final String hex = Integer.toHexString(0xff & b);
                if (hex.length() == 1) {
                    hexString.append('0');
                }
                hexString.append(hex);
            }

            return hexString.toString();

        } catch (final NoSuchAlgorithmException e) {
            // Eccezione specifica invece di RuntimeException generica
            throw new PasswordHashingException("Errore durante l'hashing della password", e);
        }
    }
}
