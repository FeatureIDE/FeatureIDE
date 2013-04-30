This project has its origin at

http://verifythis.cost-ic0701.org/post?pid=database-system-for-managing-exams

(posted by Timo Eifler) and we extracted the features BonusPoints, BackOut, and Statistics in a feature-oriented fashion.

Smaller modifications were needed which are basically refactorings:

* I created a new method validStudent() which is refined by feature BackOut. This is a "pure" method and used in several contracts.
* I created a new method getBonusPoints() similarly to the method above.
* I split the invariant in ExamDataBase into smaller peaces.

(C) Thomas Thüm, 2011