package ElevatorSystem;

public class Person {

	private int weight;

	private int origin;

	private int destination;

	private String name;

	private boolean destinationReached = false;

	public int getWeight() {
		return weight;
	}

	public Person(String name, int weight, int origin, int destination, Environment env) {
		super();
		this.name = name;
		this.weight = weight;
		this.origin = origin;
		this.destination = destination;
		env.getFloor(origin).addWaitingPerson(this);
	}

	public String getName() {
		return name;
	}
	public int getOrigin() {
		return origin;
	}

	public int getDestination() {
		return destination;
	}

	public void leaveElevator() {
		this.destinationReached = true;
	}

	public boolean isDestinationReached() {
		return destinationReached;
	}
	
	public void enterElevator(Elevator e) {
		
		e.pressInLiftFloorButton(destination);
	}
}
