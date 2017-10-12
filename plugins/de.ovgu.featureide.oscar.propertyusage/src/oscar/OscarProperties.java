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
 * Based on oscar/src/main/java/oscar/OscarProperties.java
 * Used to ensure properties are loaded in the same manner as OSCAR EMR.
 * Modifications by Raymond Rusk (rrusk)
 */

package oscar;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Date;
import java.util.HashSet;
import java.util.Properties;
import java.util.Set;


/**
 * This class will hold OSCAR & CAISI properties. It is a singleton class. Do not instantiate it, use the method getInstance(). Every time the properties file changes, tomcat must be restarted.
 */
public class OscarProperties extends Properties {
	private static final long serialVersionUID = -5965807410049845132L;
	private static OscarProperties oscarProperties = new OscarProperties();
	private static final Set<String> activeMarkers = new HashSet<String>(Arrays.asList(new String[] { "true", "yes", "on" }));

	/**
	 * @return OscarProperties the instance of OscarProperties
	 */
	public static OscarProperties getInstance() {
		return oscarProperties;
	}

	public String getProperty(String key) {
		return super.getProperty(key);
	}

	public String getProperty(String key, String defaultValue) {
		return super.getProperty(key, defaultValue);
	}

	/* If cant find the file, inform and continue */
	/*
	 * private OscarProperties() {
	 * 
	 * InputStream is = getClass().getResourceAsStream("/oscar_mcmaster.properties"); try { load(is); } catch (Exception e) { MiscUtils.getLogger().debug("Error, file oscar_mcmaster.properties not found.");
	 * MiscUtils.getLogger().debug("This file must be placed at WEB-INF/classes."); }
	 * 
	 * try{ is.close(); } catch (IOException e) { MiscUtils.getLogger().debug("IO error."); MiscUtils.getLogger().error("Error", e); } } //OscarProperties - end
	 */

	/* Do not use this constructor. Use getInstance instead */
	private OscarProperties() {
		System.out.println("OSCAR PROPS CONSTRUCTOR");

		try {
			readFromFile("../../src/resources/oscar_mcmaster.properties");

			String overrideProperties = System.getProperty("oscar_override_properties");
			if (overrideProperties != null) {
				System.out.println("Applying override properties : "+overrideProperties);
				readFromFile(overrideProperties);
			}
		} catch (IOException e) {
			System.out.println("Error" + e);
		}
	}

	public void readFromFile(String url) throws IOException {
		InputStream is = getClass().getResourceAsStream(url);
		if (is == null) is = new FileInputStream(url);

		try {
			load(is);
		} finally {
			is.close();
		}
	}

	/*
	 * Check to see if the properties to see if that property exists.
	 */
	public boolean hasProperty(String key) {
		boolean prop = false;
		String propertyValue = getProperty(key.trim());
		if (propertyValue != null) {
			prop = true;
		}
		return prop;
	}

	/**
	 * Will check the properties to see if that property is set and if it's set to the given value. 
	 * If it is method returns true if not method returns false. 
	 * This method returns positive response on any "true", "yes" or "on" values.
	 * 
	 * @param key key of property
	 * @param val value that will cause a true value to be returned
	 * @return boolean
	 */
	public boolean getBooleanProperty(String key, String val) {
		key = key==null ? null : key.trim();
		val = val==null ? null : val.trim();
		// if we're checking for positive value, any "active" one will do
		if (val != null && activeMarkers.contains(val.toLowerCase())) {
			return isPropertyActive(key);
		}
		
		return getProperty(key, "").trim().equalsIgnoreCase(val);
	}

	/**
	 * Will check the properties to see if that property is set and if it's set to "true", "yes" or "on". 
	 * If it is method returns true if not method returns false.
	 * 
	 * @param key key of property
	 * @return boolean whether the property is active
	 */
	public boolean isPropertyActive(String key) {
		key = key==null ? null : key.trim();
		return activeMarkers.contains(getProperty(key, "").trim().toLowerCase());
	}

	/*
	 * Comma delimited spring configuration modules Options: Caisi,Indivo Caisi - Required to run the Caisi Shelter Management System Indivo - Indivo PHR record. Required for integration with Indivo.
	 */

	/*
	 * not being used - commenting out public final String ModuleNames = "ModuleNames";
	 */

	public Date getStartTime() {
		String str = getProperty("OSCAR_START_TIME");
		Date ret = null;
		try {
			ret = new Date(Long.parseLong(str));
		} catch (Exception e) {/* No Date Found */
		}
		return ret;
	}

	public boolean isTorontoRFQ() {
		return isPropertyActive("TORONTO_RFQ");
	}

	public boolean isProviderNoAuto() {
		return isPropertyActive("AUTO_GENERATE_PROVIDER_NO");
	}

	public boolean isPINEncripted() {
		return isPropertyActive("IS_PIN_ENCRYPTED");
	}

	public boolean isSiteSecured() {
		return isPropertyActive("security_site_control");
	}

	public boolean isAdminOptionOn() {
		return isPropertyActive("with_admin_option");
	}

	public boolean isLogAccessClient() {
		return isPropertyActive("log_accesses_of_client");
	}

	public boolean isLogAccessProgram() {
		return isPropertyActive("log_accesses_of_program");
	}

	public boolean isAccountLockingEnabled() {
		return isPropertyActive("ENABLE_ACCOUNT_LOCKING");
	}
	
	public boolean isOntarioBillingRegion() {
		return ( "ON".equals( getProperty("billregion") ) );
	}
	
	public boolean isBritishColumbiaBillingRegion() {
		return ( "BC".equals( getProperty("billregion") ) );
	}
	
	public boolean isAlbertaBillingRegion() {
		return ( "AB".equals( getProperty("billregion") ) );
	}

	public boolean isCaisiLoaded() {
		return isPropertyActive("caisi");
	}

	public String getDbType() {
		return getProperty("db_type");
	}

	public String getDbUserName() {
		return getProperty("db_username");
	}

	public String getDbPassword() {
		return getProperty("db_password");
	}

	public String getDbUri() {
		return getProperty("db_uri");
	}

	public String getDbDriver() {
		return getProperty("db_driver");
	}

	public static String getBuildDate() {
		return oscarProperties.getProperty("buildDateTime");
	}

	public static String getBuildTag() {
		return oscarProperties.getProperty("buildtag");
	}

	public boolean isOscarLearning() {
		return isPropertyActive("OSCAR_LEARNING");
	}
	
	public boolean faxEnabled() {
		return isPropertyActive("enableFax");
	}
	
	public boolean isRxFaxEnabled() {
		return isPropertyActive("rx_fax_enabled");
	}
		
	public boolean isConsultationFaxEnabled() {
		return isPropertyActive("consultation_fax_enabled");
	}
	
	public boolean isEFormSignatureEnabled() {
		return isPropertyActive("eform_signature_enabled");
	}
	
	public boolean isEFormFaxEnabled() {
		return isPropertyActive("eform_fax_enabled");
	}
	
	public boolean isFaxEnabled() {
		return faxEnabled() || isRxFaxEnabled() || isConsultationFaxEnabled() || isEFormFaxEnabled();
	}

	public boolean isRxSignatureEnabled() {
		return isRxFaxEnabled() || isPropertyActive("rx_signature_enabled");
	}
	
	public boolean isConsultationSignatureEnabled() {
		return isPropertyActive("consultation_signature_enabled");
	}
	
	public boolean isSpireClientEnabled() {
		return isPropertyActive("SPIRE_CLIENT_ENABLED");
	}
	
	public int getSpireClientRunFrequency() {
		String prop = getProperty("spire_client_run_frequency");
		return Integer.parseInt(prop);
	}
	
	public String getSpireServerUser() {
		return getProperty("spire_server_user");
	}
	
	public String getSpireServerPassword() {
		return getProperty("spire_server_password");
	}
	
	public String getSpireServerHostname() {
		return getProperty("spire_server_hostname");
	}
	
	public String getSpireDownloadDir() {
		return getProperty("spire_download_dir");
	}

	public String getHL7A04BuildDirectory() {
		return getProperty("hl7_a04_build_dir");
	}
	
	public String getHL7A04SentDirectory() {
		return getProperty("hl7_a04_sent_dir");
	}
	
	public String getHL7A04FailDirectory() {
		return getProperty("hl7_a04_fail_dir");
	}
	
	public String getHL7SendingApplication() {
		return getProperty("HL7_SENDING_APPLICATION");
	}
	
	public String getHL7SendingFacility() {
		return getProperty("HL7_SENDING_FACILITY");
	}
	
	public String getHL7ReceivingApplication() {
		return getProperty("HL7_RECEIVING_APPLICATION");
	}
	
	public String getHL7ReceivingFacility() {
		return getProperty("HL7_RECEIVING_FACILITY");
	}
	
	public boolean isHL7A04GenerationEnabled() {
		return isPropertyActive("HL7_A04_GENERATION");
	}
	
	public boolean isEmeraldHL7A04TransportTaskEnabled() {
		return isPropertyActive("EMERALD_HL7_A04_TRANSPORT_TASK");
	}
	
	public String getEmeraldHL7A04TransportAddr() {
		return getProperty("EMERALD_HL7_A04_TRANSPORT_ADDR");
	}
	
	public int getEmeraldHL7A04TransportPort() {
		String prop = getProperty("EMERALD_HL7_A04_TRANSPORT_PORT", "3987"); // default to port 3987
		return Integer.parseInt(prop);
	}

	public static String getIntakeProgramAccessServiceId() {
		return oscarProperties.getProperty("form_intake_program_access_service_id");
	}
	
	public static String getIntakeProgramCashServiceId() {
		return oscarProperties.getProperty("form_intake_program_cash_service_id");
	}
	
	public static String getIntakeProgramAccessFId() {
		return oscarProperties.getProperty("form_intake_program_access_fid");
	}
	
	public static String getConfidentialityStatement() {
		String result = null;
		int count = 1;
		String statement = null;
		while ((statement = oscarProperties.getProperty("confidentiality_statement.v" + count)) != null) {
			count++;
			result = statement;
		}
		return result;
	}
	
	public static String getIntakeProgramCashFId() {
		return oscarProperties.getProperty("form_intake_program_cash_fid");
	}
	
	public static boolean isLdapAuthenticationEnabled() {
		return Boolean.parseBoolean(oscarProperties.getProperty("ldap.enabled"));
	}
}
