module MAPEpatterns

import StandardLibrary
import LTLlibrary

export *

signature:
	derived correctStep: Prod(Boolean, Boolean, Powerset(Boolean)) -> Boolean
	derived both: Prod(Boolean, Boolean) -> Boolean
	derived requires: Prod(Boolean, Powerset(Boolean)) -> Boolean
	derived ensures: Prod(Boolean, Powerset(Boolean)) -> Boolean

definitions:
	function correctStep($p in Boolean, $q in Boolean, $s in Powerset(Boolean)) =
		$p implies u((forall $e in $s with not($e)), $q)

	function both($p in Boolean, $q in Boolean) =
		($p implies (f($q) or o($q))) and ($q implies (f($p) or o($p)))

	function requires($p in Boolean, $s in Powerset(Boolean)) =
		$p implies (forall $e in $s with o($e))

	function ensures($p in Boolean, $s in Powerset(Boolean)) =
		$p implies (forall $e in $s with f($e))