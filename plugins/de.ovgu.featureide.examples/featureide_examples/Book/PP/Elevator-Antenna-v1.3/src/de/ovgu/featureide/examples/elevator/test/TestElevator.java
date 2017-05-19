package de.ovgu.featureide.examples.elevator.test;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.Queue;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.examples.elevator.core.controller.ControlUnit;
import de.ovgu.featureide.examples.elevator.core.controller.ITickListener;
//#if CallButtons
import de.ovgu.featureide.examples.elevator.core.controller.Request;
//#endif
import de.ovgu.featureide.examples.elevator.core.model.Elevator;

public class TestElevator {

	private final class TestListener implements ITickListener {
		private final ControlUnit controller;
		private String wrongResult = null;

		private TestListener(ControlUnit controller) {
			this.controller = controller;
		}

		public void onTick(Elevator elevator) {
			if (!expectedResult.isEmpty()) {
				final String result = elevator.getCurrentFloor() + " " + elevator.getCurrentState();
				if (result.equals(expectedResult.peek())) {
					expectedResult.poll();
				} else {
					wrongResult = result;
					controller.run = false;
				}
			} else {
				controller.run = false;
			}
		}

		//#if CallButtons
		@Override
		public void onRequestFinished(Elevator elevator, Request request) {				
		}
		//#endif
	}

	@Before
	public void setUp() throws Exception {
		ControlUnit.TIME_DELAY = 0;
	}

	@After
	public void tearDown() throws Exception {
	}
	
	private Queue<String> expectedResult = new LinkedList<>(Arrays.asList(
			//#if Sabbath
//@			"1 MOVING_UP",
//@			"1 FLOORING",
//@			"2 MOVING_UP",
//@			"2 FLOORING",
//@			"3 MOVING_UP",
//@			"3 FLOORING",
//@			"2 MOVING_DOWN",
//@			"2 FLOORING",
//@			"1 MOVING_DOWN",
//@			"1 FLOORING",
//@			"0 MOVING_DOWN",
//@			"0 FLOORING",
//@			"1 MOVING_UP",
//@			"1 FLOORING"
			//#elif FIFO
//@			"1 MOVING_UP",
//@			"2 MOVING_UP",
//@			"3 MOVING_UP",
//@			"3 FLOORING",
//@			"2 MOVING_DOWN",
//@			"2 FLOORING",
//@			"2 FLOORING"
			//#else
			"1 MOVING_UP",
			"2 MOVING_UP",
			"2 FLOORING",
			"3 MOVING_UP",
			"3 FLOORING",
			"3 FLOORING"
			//#endif
	));

	@Test
	public void test() {
		final ControlUnit controller = new ControlUnit(new Elevator(3));
		
		final TestListener listener = new TestListener(controller);
		controller.addTickListener(listener);

		//#if CallButtons
		controller.trigger(new Request(3));
		try {
			Thread.sleep(1);
		} catch (InterruptedException e1) {
		}
		controller.trigger(new Request(2));
		//#endif
		
		Thread thread = new Thread(controller);
		thread.start();
		try {
			thread.join();
		} catch (InterruptedException e) {
		}
		assertEquals(expectedResult.poll(), listener.wrongResult);
	}

}
