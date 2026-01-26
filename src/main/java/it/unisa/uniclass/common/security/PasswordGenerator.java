package it.unisa.uniclass.common.security;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.security.SecureRandom;

public class PasswordGenerator {

    private static final Logger LOGGER = LoggerFactory.getLogger(PasswordGenerator.class);

    public static String generatePassword(int length) {
        if (length < 8) {
            throw new IllegalArgumentException("La lunghezza della password deve essere almeno 8 caratteri.");
        }

        // Caratteri suddivisi per tipo
        final String upperCase = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        final String lowerCase = "abcdefghijklmnopqrstuvwxyz";
        final String digits = "0123456789";
        final String specialChars = "@#$€&%";

        // Insieme completo di caratteri
        final String allChars = upperCase + lowerCase + digits + specialChars;

        // StringBuilder per la password
        final StringBuilder password = new StringBuilder(length);

        // SecureRandom per generare numeri casuali sicuri
        final SecureRandom random = new SecureRandom();

        // Garantisce che ci sia almeno un carattere di ogni tipo
        password.append(upperCase.charAt(random.nextInt(upperCase.length())));
        password.append(lowerCase.charAt(random.nextInt(lowerCase.length())));
        password.append(digits.charAt(random.nextInt(digits.length())));
        password.append(specialChars.charAt(random.nextInt(specialChars.length())));

        // Riempie il resto della password con caratteri casuali
        for (int i = 4; i < length; ++i) {
            password.append(allChars.charAt(random.nextInt(allChars.length())));
        }

        // Mescola i caratteri per evitare una struttura prevedibile
        return shuffleString(password.toString(), random);
    }

    private static String shuffleString(String input, SecureRandom random) {
        final char[] characters = input.toCharArray();
        for (int i = characters.length - 1; i > 0; i--) {
            final int j = random.nextInt(i + 1);
            final char temp = characters[i];
            characters[i] = characters[j];
            characters[j] = temp;
        }
        return new String(characters);
    }

    public static void main(String[] args) {
        final String password = generatePassword(12);
        LOGGER.info("Password generata: {}", password);
    }
}
