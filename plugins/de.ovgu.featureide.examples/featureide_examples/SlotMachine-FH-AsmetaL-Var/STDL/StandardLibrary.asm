module StandardLibrary

export *

signature :
	/*----------- Domains --------------*/
	anydomain Any
	anydomain D
	anydomain D1
	anydomain D2
	anydomain D3
	anydomain D4
	anydomain D5
	anydomain D6
	anydomain D7
	anydomain D8
	anydomain D9

	basic domain Complex
	basic domain Real
	basic domain Integer
	basic domain Natural
	basic domain Char
	basic domain String
	basic domain Boolean
	basic domain Undef
	
	abstract domain Agent
	abstract domain Reserve

	// ************** very nasty functions
	// used to print something
	static print: D -> Integer
	static print: Prod(D, D1) -> Integer
	static print: Prod(D, D1, D2) -> Integer
	static print: Prod(D, D1, D2, D3) -> Integer
	static print: Prod(D, D1, D2, D3, D4) -> Integer
	static print: Prod(D, D1, D2, D3, D4, D5) -> Integer
	static print: Prod(D, D1, D2, D3, D4, D5, D6) -> Integer
	static print: Prod(D, D1, D2, D3, D4, D5, D6, D7) -> Integer
	static print: Prod(D, D1, D2, D3, D4, D5, D6, D7, D8) -> Integer
	static print: Prod(D, D1, D2, D3, D4, D5, D6, D7, D8, D9) -> Integer
	// **************

/*-----------Reserved 0-ary function--------------------*/
	controlled result: Any

/*----------- ASM Functions on all Domains -------------*/
	static eq: Prod(D,D) -> Boolean
	static neq: Prod(D,D) -> Boolean
	static isDef: D -> Boolean
	static isUndef: D -> Boolean

/*----------- Relational operators with mixed arithmetic domains -----*/
	static eq: Prod(Natural, Integer) -> Boolean
	static eq: Prod(Integer, Natural) -> Boolean
	static eq: Prod(Real, Natural) -> Boolean
	static eq: Prod(Natural, Real) -> Boolean
	static eq: Prod(Real, Integer) -> Boolean
	static eq: Prod(Integer, Real) -> Boolean

/*----------- Basic Functions on Complex--------------*/	
	static re: Complex -> Real
	static im: Complex -> Real
	static plus: Prod(Complex, Complex) -> Complex
	static minus: Prod (Complex, Complex) -> Complex
	static mult: Prod (Complex, Complex) -> Complex
	static div: Prod (Complex, Complex) -> Complex
	static minus: Complex -> Complex
	static norm: Complex -> Complex
	static iszero: Complex -> Boolean
	static toString: Complex -> String

/*----------- Basic Functions on Real--------------*/
	static plus: Real -> Real
	static plus: Prod(Real, Real) -> Real
	static minus: Real -> Real
	static minus: Prod(Real, Real) -> Real
	static mult: Prod (Real, Real) -> Real
	static div: Prod (Real, Real) -> Real
	static abs: Real -> Real
	static floor: Real -> Integer
	static round: Real -> Integer
	static sqrt: Real -> Real
	static pwr: Prod (Real, Real) -> Real
	static max: Prod (Real, Real) -> Real
	static min: Prod (Real, Real) -> Real
	static toString: Real -> String
	static lt: Prod (Real, Real) -> Boolean
	static gt: Prod (Real, Real) -> Boolean
	static le: Prod (Real, Real) -> Boolean
	static ge: Prod (Real, Real) -> Boolean
	//CONVERSION
	static rtoi: Real -> Integer
	static rton: Real -> Natural

	// returns the range between two numbers
	static range: Prod(Natural, Natural) -> Powerset(Natural)

/*----------- Basic Functions on Integer --------------*/
	static plus: Integer -> Integer
	static plus: Prod(Integer, Integer) -> Integer
	static minus: Integer -> Integer
	static minus: Prod(Integer, Integer) -> Integer
	static mult: Prod(Integer, Integer) -> Integer
	static div: Prod(Integer, Integer) -> Real
	static abs: Integer -> Integer
	static idiv: Prod(Integer, Integer) -> Integer
	static mod: Prod(Integer, Integer) -> Integer
	static mod: Prod(Integer, Natural) -> Integer
	static mod: Prod(Natural, Integer) -> Integer
	static max: Prod(Integer, Integer) -> Integer
	static min: Prod(Integer, Integer) -> Integer
	static toString: Integer -> String
	static lt: Prod(Integer, Integer) -> Boolean
	static gt: Prod(Integer, Integer) -> Boolean
	static le: Prod(Integer, Integer) -> Boolean
	static ge: Prod(Integer, Integer) -> Boolean
	//CONVERSION
	static itor: Integer -> Real
	static iton: Integer -> Natural

/*----------- Basic Functions on Natural --------------*/
	static plus: Prod(Natural, Natural) -> Natural
	static minus: Prod(Natural, Natural) -> Integer
	static mult: Prod(Natural, Natural) -> Natural
	static div: Prod(Natural, Natural) -> Real
	static idiv: Prod(Natural, Natural) -> Natural
	static mod: Prod(Natural, Natural) -> Natural
	static max: Prod(Natural, Natural) -> Natural
	static min: Prod(Natural, Natural) -> Natural
	static toString: Natural -> String
	static lt: Prod(Natural, Natural) -> Boolean
	static gt: Prod(Natural, Natural) -> Boolean
	static le: Prod(Natural, Natural) -> Boolean
	static ge: Prod(Natural, Natural) -> Boolean
	//CONVERSION
	static ntoi: Natural -> Integer
	static ntor: Natural -> Real

/*----------- Basic Functions on Char --------------*/
	static toString: Char -> String
	static lt: Prod(Char, Char) -> Boolean
	static gt: Prod(Char, Char) -> Boolean
	static le: Prod(Char, Char) -> Boolean
	static ge: Prod(Char, Char) -> Boolean

/*----------- Basic Functions on String --------------*/
	static size: String -> Integer
	static plus: Prod(String, String) -> String
	static concat: Prod(String, String) -> String
	static toUpper: String -> String
	static toLower: String -> String
	static subString: Prod(String, Integer, Integer) -> String
	static contains: Prod(String, String) -> Boolean //Does the first argument contain the second argument?
	static toInteger: String -> Integer
	static toNatural: String -> Natural
	static toReal: String -> Real
	static toComplex: String -> Complex
	static toChar: String -> Char
	static split: Prod(String, String) -> Seq(String)

/*----------- Basic Functions on Boolean --------------*/
	static or: Prod(Boolean, Boolean) -> Boolean
	static xor: Prod(Boolean, Boolean) -> Boolean
	static and: Prod(Boolean, Boolean) -> Boolean
	static not: Boolean -> Boolean
	static implies: Prod(Boolean, Boolean) -> Boolean
	static iff: Prod(Boolean, Boolean) -> Boolean

/*----------- Basic Functions on Agent--------------*/	
	static id: Agent -> String
	static getAgent: String -> Agent
	static program: Agent -> Rule
	controlled self: Agent

/*----------- Basic Functions on Sets--------------*/
	static size: Powerset(D)-> Integer
	static contains: Prod(Powerset(D), D) -> Boolean
	static notin: Prod(Powerset(D), D)-> Boolean
	static allin: Prod(Powerset(D), Powerset(D)) -> Boolean
	static notallin: Prod(Powerset(D), Powerset(D)) -> Boolean
	static isEmpty: Powerset(D) -> Boolean
	static notEmpty: Powerset(D) -> Boolean
	static sum: Powerset(D) -> D
	static union: Prod(Powerset(D), Powerset(D)) -> Powerset(D)
	static union: Prod(Powerset(D), Bag(D)) -> Bag(D)
	static equality: Prod(Powerset(D), Powerset(D)) -> Boolean
	static intersection: Prod(Powerset(D), Powerset(D)) -> Powerset(D)
	static intersection: Prod(Powerset(D), Bag(D)) -> Powerset(D)
	static difference: Prod(Powerset(D), Powerset(D)) -> Powerset(D)
	static including: Prod(Powerset(D), D) -> Powerset(D)
	static excluding: Prod(Powerset(D), D) -> Powerset(D)
	static symmetricDifference: Prod(Powerset(D), Powerset(D)) -> Powerset(D)
	//static count: Prod(Powerset(D),D) -> Natural // PA 18/12/2010 Forse non serve sui sets. Un elemento o appartiene o non appartiene ad un set. contains dovrebbe essere sufficiente. 
	static asSequence: Powerset(D) -> Seq(D)
	static asBag: Powerset(D) -> Bag(D)

	//Return one element of the given set, behavior undefined if set is empty
	static chooseone: Powerset(D) -> D

/*----------- Basic Functions on Sequences--------------*/
	static count: Prod(Seq(D),D) -> Natural
	static length: Seq(D) -> Integer
	static isEmpty: Seq(D) -> Boolean
	static contains: Prod(Seq(D), D)-> Boolean
	static union: Prod(Seq(D), Seq(D)) -> Seq(D)
	static append: Prod(Seq(D), D) -> Seq(D)
	static prepend: Prod(D, Seq(D)) -> Seq(D)
	static insertAt: Prod(Seq(D), Natural, D) -> Seq(D)
	static subSequence: Prod(Seq(D), Natural, Natural) -> Seq(D)
	static at: Prod(Seq(D),Natural) -> D
	static indexOf: Prod(Seq(D),D) -> Integer
	static first: Seq(D) -> D
	static last: Seq(D) -> D
	static asBag: Seq(D) -> Bag(D)
	static asSet: Seq(D) -> Powerset(D)
	static excluding: Prod(Seq(D),D) -> Seq(D)
	static tail: Seq(D) -> Seq(D)
	static replaceAt: Prod(Seq(D),Natural,D) -> Seq(D)//Da decidere se tenerla. Suggerita da Luca Baggio.

/*----------- Basic Functions on Bags--------------*/
	static union: Prod(Bag(D),Bag(D))->Bag(D)
	static union: Prod(Bag(D),Powerset(D))->Bag(D)
	static contains: Prod(Bag(D), D)-> Boolean
	static intersection: Prod(Bag(D),Bag(D))->Bag(D)
	static intersection: Prod(Bag(D),Powerset(D))->Bag(D)
	static including: Prod(Bag(D),D) -> Bag(D)
	static excluding: Prod(Bag(D),D) -> Bag(D)
	static count: Prod(Bag(D),D) -> Natural
	static asSequence: Bag(D) -> Seq(D)
	static asSet: Bag(D) -> Powerset(D)
	static sum: Bag(D) -> D//PA 2010/12/15 tenerla?

/*----------- Basic Functions on Maps--------------*/
	static merge: Prod(Map(D1,D2),Map(D1,D2)) -> Map(D1,D2)
	static assign: Prod(Map(D1,D2),D1,D2) -> Map(D1,D2)
	static at: Prod(Map(D1,D2),D1) -> D2

/*----------- Basic Functions on Products--------------*/
	static at: Prod(Prod(D1,D2),Natural) -> Any
	static at: Prod(Prod(D1,D2,D3),Natural) -> Any
	static at: Prod(Prod(D1,D2,D3,D4),Natural) -> Any

	static indexOf: Prod(Prod(D1,D2),Any) -> Integer
	static indexOf: Prod(Prod(D1,D2,D3),Any) -> Integer
	static indexOf: Prod(Prod(D1,D2,D3,D4),Any) -> Integer

	static first: Prod(D1,D2) -> D1
	static first: Prod(D1,D2,D3) -> D1
	static first: Prod(D1,D2,D3,D4) -> D1
	static first: Prod(D1,D2,D3,D4,D5) -> D1
	static first: Prod(D1,D2,D3,D4,D5,D6) -> D1
	static first: Prod(D1,D2,D3,D4,D5,D6,D7) -> D1
	static first: Prod(D1,D2,D3,D4,D5,D6,D7,D8) -> D1
	static first: Prod(D1,D2,D3,D4,D5,D6,D7,D8,D9) -> D1

	static second: Prod(D1,D2) -> D2
	static second: Prod(D1,D2,D3) -> D2
	static second: Prod(D1,D2,D3,D4) -> D2
	static second: Prod(D1,D2,D3,D4,D5) -> D2
	static second: Prod(D1,D2,D3,D4,D5,D6) -> D2
	static second: Prod(D1,D2,D3,D4,D5,D6,D7) -> D2
	static second: Prod(D1,D2,D3,D4,D5,D6,D7,D8) -> D2
	static second: Prod(D1,D2,D3,D4,D5,D6,D7,D8,D9) -> D2

	static third: Prod(D1,D2,D3) -> D3
	static third: Prod(D1,D2,D3,D4) -> D3
	static third: Prod(D1,D2,D3,D4,D5) -> D3
	static third: Prod(D1,D2,D3,D4,D5,D6) -> D3
	static third: Prod(D1,D2,D3,D4,D5,D6,D7) -> D3
	static third: Prod(D1,D2,D3,D4,D5,D6,D7,D8) -> D3
	static third: Prod(D1,D2,D3,D4,D5,D6,D7,D8,D9) -> D3

	static fourth: Prod(D1,D2,D3,D4) -> D4
	static fourth: Prod(D1,D2,D3,D4,D5) -> D4
	static fourth: Prod(D1,D2,D3,D4,D5,D6) -> D4
	static fourth: Prod(D1,D2,D3,D4,D5,D6,D7) -> D4
	static fourth: Prod(D1,D2,D3,D4,D5,D6,D7,D8) -> D4
	static fourth: Prod(D1,D2,D3,D4,D5,D6,D7,D8,D9) -> D4

	static fifth: Prod(D1,D2,D3,D4,D5) -> D5
	static fifth: Prod(D1,D2,D3,D4,D5,D6) -> D5
	static fifth: Prod(D1,D2,D3,D4,D5,D6,D7) -> D5
	static fifth: Prod(D1,D2,D3,D4,D5,D6,D7,D8) -> D5
	static fifth: Prod(D1,D2,D3,D4,D5,D6,D7,D8,D9) -> D5

	static sixth: Prod(D1,D2,D3,D4,D5,D6) -> D6
	static sixth: Prod(D1,D2,D3,D4,D5,D6,D7) -> D6
	static sixth: Prod(D1,D2,D3,D4,D5,D6,D7,D8) -> D6
	static sixth: Prod(D1,D2,D3,D4,D5,D6,D7,D8,D9) -> D6

	static seventh: Prod(D1,D2,D3,D4,D5,D6,D7) -> D7
	static seventh: Prod(D1,D2,D3,D4,D5,D6,D7,D8) -> D7
	static seventh: Prod(D1,D2,D3,D4,D5,D6,D7,D8,D9) -> D7

	static eighth: Prod(D1,D2,D3,D4,D5,D6,D7,D8) -> D8
	static eighth: Prod(D1,D2,D3,D4,D5,D6,D7,D8,D9) -> D8

	static ninth: Prod(D1,D2,D3,D4,D5,D6,D7,D8,D9) -> D9

	static toString: D -> String


	static pre: D -> D

definitions:
