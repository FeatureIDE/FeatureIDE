//import gov.nasa.jpf.jvm.Verify;

import java.util.List; 
import TestSpecifications.SpecificationManager;

public class PL_Interface_impl implements PL_Interface {
	public static void main(String[] args) {
		try {
			(new PL_Interface_impl()).start(-1,-1);
			System.out.println("no Exception");
		} catch (Throwable e) {
			System.out.println("Caught Exception: " + e.getClass() + " " + e.getMessage());
			e.printStackTrace();
		}
	}
	public void start(int specification, int variation) {
		if (variation==-1) {
			if (specification==1) {
				test_1_addressBook_encrypt();
			} else if (specification==3) {
				test_3_sign_verify();
			} else if (specification==4) {
				test_4_sign_forward();
			} else if (specification==6) {
				test_6_encrypt_decrypt();
			} else if (specification==7) {
				test_7_encrypt_verify();
			} else if (specification==8) {
				test_8_Encrypt_Autoresponder();
			} else if (specification==9) {
				test_9_Encrypt_Forward();
			} else if (specification==11) {
				test_11_decrypt_autoresponder();
			} else if (specification==27) {
				test_27_verify_forward();
			}
			if (Test_Actions.executedUnimplementedAction) {
				System.out.println("Executed an unimplemented action!!");
			}
		} else {
			runRandomActions(variation);
		}
		//Scenario.test();
	}
	public void checkOnlySpecification(int specID) {
		SpecificationManager.checkOnlySpecification(specID);
	}
	public List<String> getExecutedActions() {
		return Test_Actions.actionHistory;
	}
	public boolean isAbortedRun() {
		return false;//Scenario.abortedRun;
	}
	
	public void runRandomActions(int maxLength) {
		Test_Actions.setup();
		int counter = 0;
		while (counter < maxLength) {
			counter++;
			
			int action = (int) (Math.random()*14);//Verify.getInt(0, 13);
			
			switch (action) {
			case 0:	Test_Actions.bobKeyAdd(); break;
			case 1: Test_Actions.bobKeyAddChuck(); break;
			case 2: Test_Actions.bobKeyChange(); break;
			case 3: Test_Actions.bobSetAddressBook(); break;
			case 4: Test_Actions.chuckKeyAdd(); break;
			case 5: Test_Actions.rjhDeletePrivateKey(); break;
			case 6: Test_Actions.rjhEnableForwarding(); break;
			case 7: Test_Actions.rjhKeyAdd(); break;
			case 8: Test_Actions.rjhKeyAddChuck(); break;
			case 9: Test_Actions.rjhKeyChange(); break;
			case 10: Test_Actions.rjhSetAutoRespond(); break;
			
			case 11: Test_Actions.bobToAlias(); break;
			case 12: Test_Actions.bobToRjh(); break;
			case 13: Test_Actions.rjhToBob(); break;
			default:
				throw new InternalError("Missed a case!");
			}
			if (Test_Actions.executedUnimplementedAction) {
				//"invalid" path
				return;
			}
		}
	}
	static void test_1_addressBook_encrypt() {
		Test_Actions.setup();
		Test_Actions.bobKeyAdd();
		Test_Actions.bobSetAddressBook();
		Test_Actions.bobToAlias();
	}
	static void test_3_sign_verify() {
		Test_Actions.setup();
		Test_Actions.rjhKeyAdd();
		Test_Actions.bobKeyChange();
		Test_Actions.bobToRjh();
	}
	static void test_4_sign_forward() {
		Test_Actions.setup();
		Test_Actions.rjhDeletePrivateKey();
		Test_Actions.rjhKeyAdd();
		Test_Actions.chuckKeyAdd();
		Test_Actions.rjhEnableForwarding();
		Test_Actions.bobToRjh();
	}
	static void test_6_encrypt_decrypt() {
		Test_Actions.setup();
		Test_Actions.bobKeyAdd();
		Test_Actions.rjhKeyChange();
		Test_Actions.bobToRjh();
	}
	static void test_7_encrypt_verify() {
		Test_Actions.setup();
		Test_Actions.bobKeyAdd();
		// rjhKeyAdd();
		Test_Actions.rjhKeyChange();
		Test_Actions.bobToRjh();
	}
	static void test_8_Encrypt_Autoresponder() {
		Test_Actions.setup();
		Test_Actions.bobKeyAdd();
		Test_Actions.rjhSetAutoRespond();
		Test_Actions.bobToRjh();
	}
	static void test_9_Encrypt_Forward() {
		Test_Actions.setup();
		Test_Actions.bobKeyAdd();
		Test_Actions.rjhEnableForwarding();
		Test_Actions.bobToRjh();
	}
	static void test_11_decrypt_autoresponder() {
		Test_Actions.setup();
		Test_Actions.bobKeyAdd();
		Test_Actions.rjhSetAutoRespond();
		Test_Actions.rjhKeyChange();
		Test_Actions.bobToRjh();
	}
	static void test_27_verify_forward() {
		Test_Actions.setup();
		Test_Actions.rjhDeletePrivateKey();
		Test_Actions.rjhKeyAdd();
		Test_Actions.rjhEnableForwarding();
		Test_Actions.bobToRjh();
	}
}
