package br.ufal.ic.colligens.models.cppchecker;

import java.util.Collection;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;

public class CppCheckerFileLogs {

	private final IFile file;
	private final Collection<CppCheckerLog> logs;

	public CppCheckerFileLogs(IFile file) {
		this.file = file;
		logs = new LinkedList<CppCheckerLog>();
	}

	public IFile getFile() {
		return file;
	}

	public Collection<CppCheckerLog> getLogs() {
		return logs;
	}

	public void addLog(CppCheckerLog log) {
		System.out.println(log.getMsg());
		logs.add(log);
	}

}
