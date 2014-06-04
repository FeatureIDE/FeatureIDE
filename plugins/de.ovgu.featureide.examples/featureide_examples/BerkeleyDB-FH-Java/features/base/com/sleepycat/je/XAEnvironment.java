package com.sleepycat.je;
import java.io.File;
import javax.transaction.xa.XAException;
import javax.transaction.xa.XAResource;
import javax.transaction.xa.Xid;
import com.sleepycat.je.txn.Txn;
import com.sleepycat.je.txn.TxnManager;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated
 * via the doc templates in the doc_src directory.
 */
public class XAEnvironment extends Environment implements XAResource {
  private static final boolean DEBUG=false;
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public XAEnvironment(  File envHome,  EnvironmentConfig configuration) throws DatabaseException {
    super(envHome,configuration);
  }
  /** 
 * Used to get the Transaction object given an XA Xid.
 */
  public Transaction getXATransaction(  Xid xid) throws DatabaseException {
    Txn ret=environmentImpl.getTxnManager().getTxnFromXid(xid);
    if (ret == null) {
      return null;
    }
    return new Transaction(this,ret);
  }
  /** 
 * Used to set the Transaction object for an XA Xid.  Public for tests.
 */
  public void setXATransaction(  Xid xid,  Transaction txn) throws DatabaseException {
    environmentImpl.getTxnManager().registerXATxn(xid,txn.getTxn(),false);
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void commit(  Xid xid,  boolean ignore) throws XAException {
    if (DEBUG) {
      System.out.println("*** commit called " + xid + "/"+ ignore);
    }
    if (xid == null) {
      return;
    }
    try {
      checkEnv();
      Transaction txn=getXATransaction(xid);
      if (txn == null) {
        throw new XAException("No transaction found for " + xid + " during commit.");
      }
      removeReferringHandle(txn);
      if (txn.getTxn().getOnlyAbortable()) {
        throw new XAException(XAException.XA_RBROLLBACK);
      }
      txn.getTxn().commit(xid);
    }
 catch (    DatabaseException DE) {
      throwNewXAException(DE);
    }
    if (DEBUG) {
      System.out.println("*** commit finished");
    }
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void end(  Xid xid,  int flags) throws XAException {
    if (DEBUG) {
      System.out.println("*** end called " + xid + "/"+ flags);
    }
    boolean tmFail=(flags & XAResource.TMFAIL) != 0;
    boolean tmSuccess=(flags & XAResource.TMSUCCESS) != 0;
    boolean tmSuspend=(flags & XAResource.TMSUSPEND) != 0;
    if ((tmFail && tmSuccess) || ((tmFail || tmSuccess) && tmSuspend)) {
      throw new XAException(XAException.XAER_INVAL);
    }
    try {
      if (DEBUG) {
        System.out.println("Transaction for " + Thread.currentThread() + " is "+ environmentImpl.getTxnManager().getTxnForThread());
      }
      Transaction txn=environmentImpl.getTxnManager().unsetTxnForThread();
      if (txn == null) {
        txn=getXATransaction(xid);
        boolean isSuspended=(txn != null) && txn.getTxn().isSuspended();
        if (!isSuspended) {
          throw new XAException(XAException.XAER_NOTA);
        }
      }
      if (tmFail) {
        txn.getTxn().setOnlyAbortable();
      }
      if (tmSuspend) {
        txn.getTxn().setSuspended(true);
      }
    }
 catch (    DatabaseException DE) {
      throwNewXAException(DE);
    }
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void forget(  Xid xid) throws XAException {
    if (DEBUG) {
      System.out.println("*** forget called");
    }
    throw new XAException(XAException.XAER_NOTA);
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean isSameRM(  XAResource rm) throws XAException {
    if (DEBUG) {
      System.out.println("*** isSameRM called");
    }
    try {
      checkEnv();
    }
 catch (    DatabaseException DE) {
      throwNewXAException(DE);
    }
    if (rm == null) {
      return false;
    }
    if (!(rm instanceof XAEnvironment)) {
      return false;
    }
    return environmentImpl == DbInternal.envGetEnvironmentImpl((XAEnvironment)rm);
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int prepare(  Xid xid) throws XAException {
    if (DEBUG) {
      System.out.println("*** prepare called");
    }
    try {
      checkEnv();
      Transaction txn=getXATransaction(xid);
      if (txn == null) {
        throw new XAException("No transaction found for " + xid + " during prepare.");
      }
      txn.getTxn().prepare(xid);
      if (DEBUG) {
        System.out.println("*** prepare returning XA_OK");
      }
      return XAResource.XA_OK;
    }
 catch (    DatabaseException DE) {
      throwNewXAException(DE);
    }
    return XAResource.XA_OK;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public Xid[] recover(  int flags) throws XAException {
    if (DEBUG) {
      System.out.println("*** recover called");
    }
    boolean tmStartRScan=(flags & XAResource.TMSTARTRSCAN) != 0;
    boolean tmEndRScan=(flags & XAResource.TMENDRSCAN) != 0;
    if ((tmStartRScan && tmEndRScan) || (!tmStartRScan && !tmEndRScan && flags != TMNOFLAGS)) {
      throw new XAException(XAException.XAER_INVAL);
    }
    try {
      checkHandleIsValid();
      checkEnv();
      if (DEBUG) {
        System.out.println("*** recover returning1");
      }
      return environmentImpl.getTxnManager().XARecover();
    }
 catch (    DatabaseException DE) {
      throwNewXAException(DE);
    }
    return null;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void rollback(  Xid xid) throws XAException {
    if (DEBUG) {
      System.out.println("*** rollback called");
    }
    try {
      checkEnv();
      Transaction txn=getXATransaction(xid);
      if (txn == null) {
        throw new XAException("No transaction found for " + xid + " during abort.");
      }
      removeReferringHandle(txn);
      txn.getTxn().abort(xid);
    }
 catch (    DatabaseException DE) {
      throwNewXAException(DE);
    }
    if (DEBUG) {
      System.out.println("*** rollback returning");
    }
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getTransactionTimeout() throws XAException {
    try {
      return (int)((getConfig().getTxnTimeout() + 999999L) / 1000000L);
    }
 catch (    Exception DE) {
      throwNewXAException(DE);
    }
    return 0;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean setTransactionTimeout(  int timeout) throws XAException {
    return false;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void start(  Xid xid,  int flags) throws XAException {
    if (DEBUG) {
      System.out.println("*** start called " + xid + "/"+ flags);
    }
    boolean tmJoin=(flags & XAResource.TMJOIN) != 0;
    boolean tmResume=(flags & XAResource.TMRESUME) != 0;
    if (xid == null || (tmJoin && tmResume) || (!tmJoin && !tmResume && flags != XAResource.TMNOFLAGS)) {
      throw new XAException(XAException.XAER_INVAL);
    }
    try {
      Transaction txn=getXATransaction(xid);
      TxnManager txnMgr=environmentImpl.getTxnManager();
      if (flags == XAResource.TMNOFLAGS) {
        if (txn == null) {
          if (DEBUG) {
            System.out.println("Transaction for XID " + xid + " being created");
          }
          txn=beginTransaction(null,null);
          setXATransaction(xid,txn);
        }
 else {
          throw new XAException(XAException.XAER_DUPID);
        }
      }
 else       if (tmJoin) {
        if (txn == null) {
          throw new XAException(XAException.XAER_NOTA);
        }
        if (txnMgr.getTxnForThread() != null) {
          throw new XAException(XAException.XAER_PROTO);
        }
      }
 else       if (tmResume) {
        if (txn == null) {
          throw new XAException(XAException.XAER_NOTA);
        }
        if (!txn.getTxn().isSuspended()) {
          throw new XAException(XAException.XAER_PROTO);
        }
        txn.getTxn().setSuspended(false);
      }
      if (DEBUG) {
        System.out.println("Setting Transaction for " + Thread.currentThread());
      }
      txnMgr.setTxnForThread(txn);
    }
 catch (    DatabaseException DE) {
      if (DEBUG) {
        System.out.println("*** start exception");
      }
      throwNewXAException(DE);
    }
    if (DEBUG) {
      System.out.println("*** start finished");
    }
  }
  private void throwNewXAException(  Exception E) throws XAException {
    XAException ret=new XAException(E.toString());
    ret.initCause(E);
    throw ret;
  }
}
