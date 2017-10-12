/**
 * Copyright (c) 2001-2002. Department of Family Medicine, McMaster University. All Rights Reserved.
 * This software is published under the GPL GNU General Public License.
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version. 
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * This software was written for the
 * Department of Family Medicine
 * McMaster University
 * Hamilton
 * Ontario, Canada
 */

/**
 * Based on oscar/src/main/java/oscar/login/Startup.java
 * Used to ensure properties are loaded in the same manner as OSCAR EMR.
 * Modifications by Raymond Rusk (rrusk)
 */

package oscar; //package oscar.login;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;


/**
 * This ContextListener is used to Initialize classes at startup - Initialize the DBConnection Pool.
 * 
 * @author Jay Gallagher
 */
public class Startup {
	private oscar.OscarProperties p = oscar.OscarProperties.getInstance();

	public void contextInitialized() {
		try {

			String contextPath = "oscar";
			String propFileName = "";

			String propName = contextPath + ".properties";

			propFileName = "../../src/resources/" + propName;
			System.out.println("looking up " + propFileName);
			// oscar.OscarProperties p = oscar.OscarProperties.getInstance();
			try {
				// This has been used to look in the users home directory that started tomcat
				p.readFromFile(propFileName);
				System.out.println("loading properties from " + propFileName);
			} catch (java.io.FileNotFoundException ex) {
				System.out.println(propFileName + " not found");
				return;
			}

			try {
				// Specify who will see new casemanagement screen
				ArrayList<String> listUsers;
				String casemgmtscreen = p.getProperty("CASEMANAGEMENT");
				if (casemgmtscreen != null) {
					String[] arrUsers = casemgmtscreen.split(",");
					listUsers = new ArrayList<String>(Arrays.asList(arrUsers));
					Collections.sort(listUsers);
				} else listUsers = new ArrayList<String>();

				System.out.println("Sets attribute CaseMgmtUsers to " + listUsers.toString());

				// Temporary Testing of new ECHART
				// To be removed
				String newDocs = p.getProperty("DOCS_NEW_ECHART");

				if (newDocs != null) {
					String[] arrnewDocs = newDocs.split(",");
					ArrayList<String> newDocArr = new ArrayList<String>(Arrays.asList(arrnewDocs));
					Collections.sort(newDocArr);
					System.out.println("Sets attribute newDocArr to " + newDocArr);
				}

				String echartSwitch = p.getProperty("USE_NEW_ECHART");
				if (echartSwitch != null && echartSwitch.equalsIgnoreCase("yes")) {
					System.out.println("Set attribute useNewEchart to true");
				}

				System.out.println("BILLING REGION : " + p.getProperty("billregion", "NOTSET"));
				System.out.println("DB PROPS: Username :" + p.getProperty("db_username", "NOTSET") + " db name: " + p.getProperty("db_name", "NOTSET"));
				p.setProperty("OSCAR_START_TIME", "" + System.currentTimeMillis());

			} catch (Exception e) {
				String s="Property file not found at:"+propFileName;
				System.out.println(s + e);
			}

			// CHECK FOR DEFAULT PROPERTIES
			String baseDocumentDir = p.getProperty("BASE_DOCUMENT_DIR");
			if (baseDocumentDir != null) {
				System.out.println("Found Base Document Dir: " + baseDocumentDir);
				checkAndSetProperty(baseDocumentDir, contextPath, "HOME_DIR", "/billing/download/");
				checkAndSetProperty(baseDocumentDir, contextPath, "DOCUMENT_DIR", "/document/");
				checkAndSetProperty(baseDocumentDir, contextPath, "eform_image", "/eform/images/");

				checkAndSetProperty(baseDocumentDir, contextPath, "oscarMeasurement_css_upload_path", "/oscarEncounter/oscarMeasurements/styles/");
				checkAndSetProperty(baseDocumentDir, contextPath, "TMP_DIR", "/export/");
				checkAndSetProperty(baseDocumentDir, contextPath, "form_record_path", "/form/records/");
				
				//HRM Directories
				checkAndSetProperty(baseDocumentDir, contextPath,"OMD_hrm","/hrm/");
				checkAndSetProperty(baseDocumentDir, contextPath,"OMD_directory" , "/hrm/OMD/");
				checkAndSetProperty(baseDocumentDir, contextPath,"OMD_log_directory" , "/hrm/logs/");
				checkAndSetProperty(baseDocumentDir, contextPath,"OMD_stored", "/hrm/stored/");
				checkAndSetProperty(baseDocumentDir, contextPath,"OMD_downloads","/hrm/sftp_downloads/");
				

			}
			
			System.out.println("LAST LINE IN contextInitialized");
		} catch (Exception e) {
			System.out.println("Unexpected error." + e);
			throw (new RuntimeException(e));
		}
	}

	// Checks for default property with name propName. If the property does not exist,
	// the property is set with value equal to the base directory, plus /, plus the webapp context
	// path and any further extensions. If the formed directory does not exist in the system,
	// it is created.
	private void checkAndSetProperty(String baseDir, String context, String propName, String endDir) {
		String propertyDir = p.getProperty(propName);
		if (propertyDir == null) {
			propertyDir = baseDir + "/" + context + endDir;
			System.out.println("Setting property " + propName + " with value " + propertyDir);
			p.setProperty(propName, propertyDir);
			// Create directory if it does not exist
			if (!(new File(propertyDir)).exists()) {
//				System.out.println("Warning! Directory does not exist:  " + propertyDir + ". Creating.");
//				boolean success = (new File(propertyDir)).mkdirs();
//				if (!success) System.out.println("An error occured when creating " + propertyDir);
			}
		}
	}

}
