package de.ovgu.featureide.fm.ui.views.constraintview;

import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;
import de.ovgu.featureide.fm.ui.views.constraintview.content.ConstraintViewFilter;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

import org.prop4j.Node;
import org.prop4j.NodeReader;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * This class tests the ConstraintViewFilter. As test for the selection in the feature model would require too much mockup, only the search is tested
 *
 * @author Soeren Viegener
 * @author Philipp Vulpius
 */
public class ConstraintViewFilterTest {
    private static final String MOCKUP_FEATURE_MODEL_FACTORY_ID = "MOCKUP_FEATURE_MODEL_FACTORY_ID";

    private FeatureModel featureModel = new FeatureModel(MOCKUP_FEATURE_MODEL_FACTORY_ID);


    /**
     * Creates a list of constraints from an array of String descriptions of those constraints
     * @param constraintStrings An array of Strings containing constraint descriptions
     * @return List of Constraints created from the descriptions
     */
    private List<Object> createConstraintList(String[] constraintStrings) {

        List<Object> constraintList = new ArrayList<>();

        List<String> featureNameList = Arrays.asList(FEATURE_NAMES);
        NodeReader nodeReader = new NodeReader();
        nodeReader.setFeatureNames(featureNameList);

        for (String c : constraintStrings) {
            Node node = nodeReader.stringToNode(c);
            if(node == null){
                System.out.println(c);
            }
            constraintList.add(new Constraint(featureModel, node));
        }
        return constraintList;
    }

    /**
     * Tests the search functionality of the filter by using different search texts and checking the results
     */
    @Test
    public void testSearch() {
        ConstraintViewFilter filter = new ConstraintViewFilter();

        List<Object> constraintList = createConstraintList(CONSTRAINT_STRINGS);
        List<Object> filteredConstraintList;

        for (int i = 0; i < SEARCH_STRINGS.length; i++) {

            filter.setSearchText(SEARCH_STRINGS[i]);
            filteredConstraintList = filterList(constraintList, filter);
            assertEquals("case " + i + ": filtered size is not expected size", SEARCH_RESULTS[i].length,
                    filteredConstraintList.size());

            for (int j = 0; j < SEARCH_RESULTS[i].length; j++) {
                assertEquals("case " + i + ": filtered object is wrong", constraintList.get(SEARCH_RESULTS[i][j])
                        , filteredConstraintList.get(j));
            }
        }
    }

    /**
     * Filters a list of objects using the given filter. This is a mockup for what would actually happen when using a content provider
     *
     * @param list List of objects to be filtered
     * @param filter ConstraintViewFilter
     * @return Filtered list of objects for which the filter returned true
     */
    private List<Object> filterList(List<Object> list, ConstraintViewFilter filter) {
        List<Object> result = new ArrayList<>();
        for (Object l : list) {
            if (filter.select(null, null, l)) {
                result.add(l);
            }
        }
        return result;
    }

    private static final String[] FEATURE_NAMES = new String[]{
            "feature0",   // 0
            "feature1",    // 1
            "feature2",    // 2
            "feature3",    // 3
            "feature4",    // 4

            "FEATURE",    // 5
            "A12345",    // 6
            "home",      // 7
            "Hallo",    // 8
            "HALLO",    // 9

            "code",      // 10
            "knife",    // 11
            "Package",    // 12
            "STRAWBERRIES"  // 13
    };
    private static final String[] CONSTRAINT_STRINGS = new String[]{
            /* 0 */ "not feature0",
            /* 1 */ "not STRAWBERRIES",
            /* 2 */ "not not FEATURE",
            /* 3 */ "not not not home",
            /* 4 */ "not A12345",

            /* 5 */ "feature0 and feature3",
            /* 6 */ "feature2 or feature2",
            /* 7 */ "knife implies STRAWBERRIES",
            /* 8 */ "code implies ( feature0 and code )",
            /* 9 */ "code and ( not code )",

            /* 10*/ "knife or ( feature0 iff feature2)",
            /* 11*/ "feature0 and feature1 and feature2 and feature3 and feature4",
            /* 12*/ "feature0 implies ( feature1 or feature2 or feature3 or feature4 )",
            /* 13*/ "Package and not feature0"
    };
    private static final String[] SEARCH_STRINGS = new String[]{
            "feature",
            "2",
            "package",
            "a",
            "b",
            "if",
            "and",
            "6",
            "++",
            ".*feature.*",
            ".*\\d"
    };
    private static final int[][] SEARCH_RESULTS = new int[][]{
            {0, 2, 5, 6, 8, 10, 11, 12, 13},
            {4, 6, 10, 11, 12},
            {13},
            {0, 1, 2, 4, 5, 6, 7, 8, 10, 11, 12, 13},
            {1, 7},
            {7, 10}, //because of knife
            {},
            {},
            {},
            {0, 2, 5, 6, 8, 10, 11, 12, 13},
            {0, 4, 5, 6, 8, 10, 11, 12, 13}

    };
}
