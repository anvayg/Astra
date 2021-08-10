/**
 * 
 */
package automata;

/**
 * @author anvaygrover
 *
 */
public abstract class FMove {
	// Source state
	public Integer from;
	// Target state
	public Integer to;

	/**
	 * Transition from state <code>from</code> to state <code>to</code>
	 */
	public FMove(Integer from, Integer to) {
		this.from = from;
		this.to = to;
	}
}
