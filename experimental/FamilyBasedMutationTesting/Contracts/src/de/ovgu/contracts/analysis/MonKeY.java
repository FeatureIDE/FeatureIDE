package de.ovgu.contracts.analysis;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.key_project.monkey.product.ui.batch.MonKeYBatchMode;
import org.key_project.monkey.product.ui.batch.MonKeYBatchModeParameters;

import de.ovgu.contracts.Contracts;
import de.ovgu.contracts.utils.FileManager;
import de.ovgu.contracts.utils.Reader;

/**
 * Runs KeY / MonKeY.
 * @author Jens Meinicke
 *
 */
// TODO set setting @ home\\.key  see folder keySetting
// TODO install KeY4Eclipse
public class MonKeY extends AbstractAnalyser {
	
	private static final int TIME_INDEX = 8;
    private static final int CLOSED_INDEX = 5;
    private static final int PROOFS_INDEX = 3;
    private static final int NODES_INDEX = 6;
    
    private static final String RES_PATH = Contracts.CONTRACTS_PATH + "keyresults\\";
	private static final Reader READER = new Reader();
	
	private MonKeYBatchMode monkey = new MonKeYBatchMode();
	private static final String[] COMMAND = new String[]{
	        MonKeYBatchModeParameters.PARAM_MAIN_WINDOW_OFF,
            MonKeYBatchModeParameters.PARAM_STOP_AT_UNCLOSABLE,
//            MonKeYBatchModeParameters.PARAM_METHOD_TREATMENT_CONTRACT, // for StringMatcher
            MonKeYBatchModeParameters.PARAM_MAX_RULES,
            "" + 500000,
            MonKeYBatchModeParameters.PARAM_ROUNDS,
            "" + ANALYSIS_ROUNDS,
            MonKeYBatchModeParameters.PARAM_OUTPUT_PATH,
            RES_PATH,
            SRC_PATH
	};
    
	
	// override runRounds because the rounds parameter can be used instead
	@Override
    public final Result runRounds() {
		return run();
	}

	/**
	 * Executes KEY.
	 */
	public final Result run() {
	    FileManager.createFolder(RES_PATH);
		try {
			monkey.start(COMMAND);
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		
		final List<File> files = FileManager.listFiles(new File(RES_PATH), new String[]{"csv"}, true);
		Result result = new Result(getName(), -1, false, new HashMap<String, String>());
		if (!files.isEmpty()) {
		    for (final File file : files) {
		        if (file.getName().equals("Average.csv")) {
    	            final String content = READER.getFileContent(file.getAbsolutePath());
    	            result = extractResult(content);
    	            break;
		        }
		    }
		    
            final int time = extractResultToFirstError(files);
            result.getAdditions().put("time to first error", "" + time);
		}
		FileManager.removeFiles(new File(RES_PATH));
		return result;
	}

    private int extractResultToFirstError(final List<File> files) {
        for (final File file : files) {
            if (file.getName().equals("src.csv")) {
                String content = READER.getFileContent(file.getAbsolutePath());
                // cut titles
                content = content.substring(content.indexOf("\n") + 1);
                String[] lines = content.split("[\n]");
                int timeToError = 0;
                for (String line : lines) {
                    String[] split = line.split("[;]");
                    String proofResult = split[6].trim();
                    if (proofResult.equals("Closed")) {
                        int time = Integer.parseInt(split[9].trim());
                        timeToError += time;
                    } else {
                        int time = Integer.parseInt(split[9].trim());
                        timeToError += time;
                        break;
                    }
                }
                return timeToError;
            }
        }
        return -1;
    }

    private Result extractResult(String content) {
        // cut titles
        content = content.substring(content.indexOf("\n") + 1);
        String[] split = content.split("[;]");
        int proofs = Integer.parseInt(split[PROOFS_INDEX].trim());
        int closed = Integer.parseInt(split[CLOSED_INDEX].trim());
        int time =   Integer.parseInt(split[TIME_INDEX].trim());
        Map<String, String> additions = new HashMap<>();
        additions.put("nodes", (split[NODES_INDEX].trim()));
        return new Result(getName(), time, proofs != closed, additions);
    }
}
