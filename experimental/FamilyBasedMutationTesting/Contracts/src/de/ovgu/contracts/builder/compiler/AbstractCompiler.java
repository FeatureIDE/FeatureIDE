package de.ovgu.contracts.builder.compiler;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.List;

import de.ovgu.contracts.Defaults;

/**
 * Interface for compilers.
 * @author Jens Meinicke
 *
 */
public abstract class AbstractCompiler implements Defaults {
    
    private static final Charset UTF_8 = Charset.availableCharsets().get("UTF-8");

	public abstract void compile(String source, String destination);
	
	protected final void process(final List<String> command) {
        try {
            final ProcessBuilder processBuilder = new ProcessBuilder(command);
            final Process process = processBuilder.start();
            try (BufferedReader input = new BufferedReader(new InputStreamReader(
                    process.getInputStream(), UTF_8));
                    BufferedReader error = new BufferedReader(new InputStreamReader(
                    process.getErrorStream(), UTF_8));) {               
                boolean x = true;
                while (x) {
                    try {
                        String line;
                        while ((line = input.readLine()) != null) {
                            System.out.println(line);
                        }
                        while ((line = error.readLine()) != null) {
                            System.out.println("JavaC Error:" + line);
                        }
                        x = false;
                    } catch (IllegalThreadStateException e) {
                        e.printStackTrace();
                    }
                }
            } catch (IOException e) {
                e.printStackTrace();
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
