package br.ufal.ic.colligens.activator;

import java.io.File;
import java.io.IOException;

/**
 * @author Thiago Emmanuel
 *
 */
public class Start {

	/**
	 * Clear the cache files
	 */
	public void SystemClear() {
		final File file = new File(Colligens.getDefault().getConfigDir().getAbsolutePath());
		try {
			delete(file);
		} catch (final IOException e) {

			e.printStackTrace();
		}
	}

	public static void delete(File file) throws IOException {

		if (file.isDirectory()) {

			// directory is empty, then delete it
			if (file.list().length == 0) {

				file.delete();

			} else {

				// list all the directory contents
				final String files[] = file.list();

				for (final String temp : files) {
					// construct the file structure
					final File fileDelete = new File(file, temp);

					// recursive delete
					delete(fileDelete);
				}

				// check the directory again, if empty then delete it
				if (file.list().length == 0) {
					file.delete();
				}
			}

		} else {
			// if file, then delete it
			file.delete();
		}
	}
}
