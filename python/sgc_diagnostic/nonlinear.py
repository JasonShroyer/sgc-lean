"""
Nonlinear SGC Extension: State-Dependent Generators and Limit Cycle Analysis

This module extends the linear SGC framework to handle genuinely nonlinear dynamics:
- State-dependent generator L(p) where transition rates depend on current distribution
- Wilson-Cowan neural mass dynamics on connectome graphs
- Floquet analysis for limit cycle stability
- Path-space defect averaging over trajectories
- Nonlinear emergence equivalence

Mathematical Foundation:
-----------------------
The linear SGC uses a fixed generator L with entropy production:
    sigma(L, pi) = (1/2) sum_{x,y} J_{xy} log(pi_x L_{xy} / pi_y L_{yx})

The nonlinear extension uses state-dependent rates k_{xy}(p):
    sigma_NL(p) = (1/2) sum_{x,y} (p_x k_{xy}(p) - p_y k_{yx}(p)) log(p_x k_{xy}(p) / p_y k_{yx}(p))

The defect becomes a functional on trajectories:
    eps_bar = (1/T) int_0^T ||(I - Pi(p(t))) L(p(t)) Pi(p(t))||_{pi(p(t))} dt

References:
-----------
- Wilson & Cowan (1972) - Neural mass models
- Schnakenberg (1976) - Network theory of microscopic irreversibility  
- Floquet (1883) - Stability of periodic solutions
- SGC formalization: src/SGC/EntropyProduction.lean
"""

import numpy as np
from typing import Tuple, Dict, List, Optional, Callable
from dataclasses import dataclass, field
from scipy.integrate import odeint, solve_ivp
from scipy.linalg import eig
import warnings


@dataclass
class NonlinearSGCProfile:
    """
    SGC profile for a nonlinear dynamical system.
    
    Extends the linear SGCProfile with:
    - Floquet exponents (stability of limit cycle)
    - Phase-dependent quantities (gamma(phi), T*(phi))
    - Path-averaged defect
    - Nonlinearity parameter
    """
    # System specification
    W: np.ndarray                    # Connectivity matrix (n x n)
    n: int = 0                       # Number of nodes
    
    # Nonlinearity parameters
    sigmoid_gain: float = 1.0        # Gain parameter for sigmoid activation
    tau: float = 1.0                 # Time constant
    
    # Linear approximation (for comparison)
    gamma_linear: float = 0.0        # Spectral gap of linearized system
    epsilon_linear: float = 0.0      # Defect of linear approximation
    
    # Floquet analysis (limit cycle stability)
    floquet_exponents: np.ndarray = None    # Floquet exponents mu_k
    floquet_period: float = 0.0             # Period T of limit cycle
    largest_floquet: float = 0.0            # Largest (most stable) exponent
    
    # Path-averaged quantities
    epsilon_path: float = 0.0        # Time-averaged defect over trajectory
    gamma_mean: float = 0.0          # Mean spectral gap over cycle
    gamma_min: float = 0.0           # Minimum gamma (bottleneck phase)
    gamma_max: float = 0.0           # Maximum gamma (fast phase)
    
    # Nonlinear predictions
    q_nonlinear: float = 1.0         # Tsallis q from nonlinear dynamics
    T_star_floquet: float = 0.0      # Validity horizon from Floquet
    
    # Trajectory data
    trajectory: np.ndarray = None    # State trajectory p(t)
    times: np.ndarray = None         # Time points
    
    # Comparison metrics
    linearity_ratio: float = 1.0     # gamma_linear / largest_floquet
    
    def __post_init__(self):
        if self.W is not None:
            self.n = len(self.W)
        if self.floquet_exponents is None:
            self.floquet_exponents = np.array([])


def sigmoid(x: np.ndarray, gain: float = 1.0, threshold: float = 0.0) -> np.ndarray:
    """
    Sigmoid activation function.
    
    For neural mass models: sigma(x) = 1 / (1 + exp(-gain * (x - threshold)))
    
    Parameters:
        x: Input values
        gain: Steepness of sigmoid (gain -> inf gives step function)
        threshold: Firing threshold
    
    Returns:
        Activated values in [0, 1]
    """
    # Clip to avoid overflow
    z = np.clip(gain * (x - threshold), -500, 500)
    return 1.0 / (1.0 + np.exp(-z))


def wilson_cowan_rhs(p: np.ndarray, t: float, W: np.ndarray, 
                     tau: float = 1.0, gain: float = 1.0,
                     external_input: np.ndarray = None) -> np.ndarray:
    """
    Wilson-Cowan neural mass dynamics on a connectome graph.
    
    dp_i/dt = (-p_i + sigma(sum_j W_{ij} p_j + I_i)) / tau
    
    This is the mean-field approximation of a stochastic neural network.
    The adjacency matrix W gives coupling strengths.
    
    Parameters:
        p: Current activity state (n,)
        t: Time (unused, for odeint compatibility)
        W: Connectivity matrix (n x n)
        tau: Time constant
        gain: Sigmoid gain (controls nonlinearity)
        external_input: External drive I_i (n,)
    
    Returns:
        dp/dt: Rate of change (n,)
    """
    n = len(p)
    if external_input is None:
        external_input = np.zeros(n)
    
    # Total input to each node
    total_input = W @ p + external_input
    
    # Wilson-Cowan dynamics
    dpdt = (-p + sigmoid(total_input, gain=gain)) / tau
    
    return dpdt


def compute_jacobian(p: np.ndarray, W: np.ndarray, 
                     tau: float = 1.0, gain: float = 1.0) -> np.ndarray:
    """
    Compute the Jacobian of Wilson-Cowan dynamics at state p.
    
    J_{ij} = d(dp_i/dt) / dp_j
           = (-delta_{ij} + gain * sigma'(input_i) * W_{ij}) / tau
    
    where sigma'(x) = sigma(x) * (1 - sigma(x)) for logistic sigmoid.
    
    Parameters:
        p: Current state (n,)
        W: Connectivity matrix (n x n)
        tau: Time constant
        gain: Sigmoid gain
    
    Returns:
        J: Jacobian matrix (n x n)
    """
    n = len(p)
    
    # Compute sigmoid and its derivative at each node
    total_input = W @ p
    s = sigmoid(total_input, gain=gain)
    s_prime = gain * s * (1 - s)  # derivative of sigmoid
    
    # Jacobian: J_{ij} = (-delta_{ij} + s'_i * W_{ij}) / tau
    J = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if i == j:
                J[i, j] = (-1.0 + s_prime[i] * W[i, j]) / tau
            else:
                J[i, j] = s_prime[i] * W[i, j] / tau
    
    return J


def state_dependent_generator(p: np.ndarray, W: np.ndarray,
                              gain: float = 1.0) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute state-dependent generator L(p) for nonlinear SGC.
    
    The transition rate from i to j depends on the current state:
        L_{ij}(p) = W_{ij} * sigma(sum_k W_{ik} p_k)
    
    This is the "effective Markov generator" at state p.
    
    Parameters:
        p: Current state distribution (n,)
        W: Connectivity matrix (n x n)
        gain: Sigmoid gain
    
    Returns:
        L: State-dependent generator (n x n)
        pi: Instantaneous stationary approximation (n,)
    """
    n = len(p)
    
    # Activation at each node
    total_input = W @ p
    activation = sigmoid(total_input, gain=gain)
    
    # State-dependent rates: L_{ij}(p) = W_{ij} * activation_i
    L = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if i != j:
                L[i, j] = W[i, j] * activation[i]
    
    # Diagonal: row sums to zero
    for i in range(n):
        L[i, i] = -np.sum(L[i, :])
    
    # Compute instantaneous stationary distribution
    # (left eigenvector of L with eigenvalue 0)
    eigenvalues, eigenvectors = eig(L.T)
    idx = np.argmin(np.abs(eigenvalues))
    pi = np.real(eigenvectors[:, idx])
    pi = np.abs(pi) / np.sum(np.abs(pi))  # normalize
    
    return L, pi


def find_limit_cycle(W: np.ndarray, tau: float = 1.0, gain: float = 1.0,
                     external_input: np.ndarray = None,
                     t_transient: float = 100.0, t_record: float = 50.0,
                     dt: float = 0.01) -> Tuple[np.ndarray, np.ndarray, float]:
    """
    Find a limit cycle of the Wilson-Cowan dynamics.
    
    Strategy:
    1. Integrate past transients
    2. Record trajectory
    3. Detect period via autocorrelation
    
    Parameters:
        W: Connectivity matrix
        tau: Time constant
        gain: Sigmoid gain
        external_input: External drive
        t_transient: Time to skip transients
        t_record: Time to record trajectory
        dt: Time step
    
    Returns:
        trajectory: State trajectory (n_times x n)
        times: Time points (n_times,)
        period: Estimated period (0 if no oscillation detected)
    """
    n = len(W)
    
    # Initial condition: small random perturbation from 0.5
    p0 = 0.5 + 0.1 * np.random.randn(n)
    p0 = np.clip(p0, 0, 1)
    
    # Integrate past transients
    t_trans = np.arange(0, t_transient, dt)
    
    def rhs(t, p):
        return wilson_cowan_rhs(p, t, W, tau, gain, external_input)
    
    sol_trans = solve_ivp(rhs, [0, t_transient], p0, t_eval=t_trans, method='RK45')
    p_end = sol_trans.y[:, -1]
    
    # Record trajectory
    t_rec = np.arange(0, t_record, dt)
    sol_rec = solve_ivp(rhs, [0, t_record], p_end, t_eval=t_rec, method='RK45')
    trajectory = sol_rec.y.T  # (n_times x n)
    times = t_rec
    
    # Estimate period via autocorrelation of first node
    signal = trajectory[:, 0] - np.mean(trajectory[:, 0])
    autocorr = np.correlate(signal, signal, mode='full')
    autocorr = autocorr[len(autocorr)//2:]  # positive lags only
    autocorr = autocorr / autocorr[0]  # normalize
    
    # Find first peak after zero crossing
    period = 0.0
    for i in range(1, len(autocorr) - 1):
        if autocorr[i] > autocorr[i-1] and autocorr[i] > autocorr[i+1] and autocorr[i] > 0.5:
            period = i * dt
            break
    
    return trajectory, times, period


def compute_floquet_exponents(W: np.ndarray, trajectory: np.ndarray, 
                              times: np.ndarray, period: float,
                              tau: float = 1.0, gain: float = 1.0) -> np.ndarray:
    """
    Compute Floquet exponents of a limit cycle.
    
    The Floquet exponents mu_k determine stability:
    - All Re(mu_k) < 0: stable limit cycle
    - Some Re(mu_k) > 0: unstable
    - mu_1 = 0 always (phase invariance)
    
    Method: Integrate the variational equation over one period
    and compute eigenvalues of the monodromy matrix.
    
    Parameters:
        W: Connectivity matrix
        trajectory: State trajectory over one period
        times: Time points
        period: Period of limit cycle
        tau: Time constant
        gain: Sigmoid gain
    
    Returns:
        floquet_exponents: Floquet exponents (n,), sorted by real part
    """
    n = len(W)
    
    if period < 1e-6:
        # No oscillation detected - return eigenvalues of fixed point Jacobian
        p_fixed = np.mean(trajectory, axis=0)
        J = compute_jacobian(p_fixed, W, tau, gain)
        eigenvalues = np.linalg.eigvals(J)
        return np.sort(np.real(eigenvalues))[::-1]
    
    # Find indices for one period
    dt = times[1] - times[0]
    n_period = int(period / dt)
    if n_period < 2:
        n_period = len(trajectory)
    
    # Integrate monodromy matrix: dM/dt = J(p(t)) @ M
    M = np.eye(n)  # Initial monodromy matrix
    
    for i in range(min(n_period, len(trajectory) - 1)):
        p = trajectory[i]
        J = compute_jacobian(p, W, tau, gain)
        # Euler step for M
        M = M + dt * J @ M
    
    # Floquet exponents from monodromy eigenvalues
    monodromy_eigenvalues = np.linalg.eigvals(M)
    
    # mu = log(lambda) / T
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        floquet_exponents = np.log(np.abs(monodromy_eigenvalues) + 1e-12) / period
    
    return np.sort(np.real(floquet_exponents))[::-1]


def compute_path_averaged_defect(W: np.ndarray, trajectory: np.ndarray,
                                  times: np.ndarray, k: int = 2,
                                  gain: float = 1.0) -> Tuple[float, List[float]]:
    """
    Compute path-averaged defect over a trajectory.
    
    eps_bar = (1/T) int_0^T ||(I - Pi) L(p(t)) Pi||_{pi(t)} dt
    
    This is the nonlinear generalization of the static defect epsilon.
    
    Parameters:
        W: Connectivity matrix
        trajectory: State trajectory (n_times x n)
        times: Time points
        k: Number of blocks for partition
        gain: Sigmoid gain
    
    Returns:
        eps_bar: Path-averaged defect
        eps_t: Instantaneous defect at each time
    """
    from sgc_diagnostic.partition import find_optimal_partition
    
    n = len(W)
    n_times = len(times)
    eps_t = []
    
    for i in range(0, n_times, max(1, n_times // 50)):  # Sample 50 points
        p = trajectory[i]
        
        # State-dependent generator at this point
        L, pi = state_dependent_generator(p, W, gain=gain)
        
        # Find optimal partition at this state
        try:
            P_star, epsilon, _ = find_optimal_partition(L, pi, k_min=k, k_max=k, n_restarts=5)
            eps_t.append(epsilon)
        except:
            eps_t.append(0.0)
    
    eps_bar = np.mean(eps_t) if eps_t else 0.0
    return eps_bar, eps_t


def compute_instantaneous_gamma(p: np.ndarray, W: np.ndarray,
                                 tau: float = 1.0, gain: float = 1.0) -> float:
    """
    Compute instantaneous spectral gap at state p.
    
    gamma(p) = second smallest eigenvalue magnitude of J(p)
    
    For limit cycles, gamma varies with phase.
    """
    J = compute_jacobian(p, W, tau, gain)
    eigenvalues = np.linalg.eigvals(J)
    eigenvalues = np.sort(np.abs(np.real(eigenvalues)))
    
    if len(eigenvalues) >= 2:
        return eigenvalues[1]  # Second smallest
    return 0.0


def nonlinear_sgc_analysis(W: np.ndarray, 
                           tau: float = 1.0,
                           gain: float = 1.0,
                           external_input: np.ndarray = None,
                           linear_gamma: float = None,
                           linear_epsilon: float = None) -> NonlinearSGCProfile:
    """
    Full nonlinear SGC analysis of a connectome.
    
    This is the main entry point for nonlinear analysis.
    
    Parameters:
        W: Connectivity matrix (n x n)
        tau: Time constant
        gain: Sigmoid gain (controls nonlinearity)
        external_input: External drive
        linear_gamma: Spectral gap from linear analysis (for comparison)
        linear_epsilon: Defect from linear analysis (for comparison)
    
    Returns:
        profile: NonlinearSGCProfile with all computed quantities
    """
    n = len(W)
    
    print(f"\n  NONLINEAR SGC ANALYSIS")
    print(f"  " + "="*60)
    print(f"  Nodes: {n}")
    print(f"  Sigmoid gain: {gain}")
    print(f"  Time constant: {tau}")
    
    # Step 1: Find limit cycle
    print(f"\n  Step 1: Finding limit cycle...")
    trajectory, times, period = find_limit_cycle(W, tau, gain, external_input)
    
    if period > 0:
        print(f"    Period detected: T = {period:.2f}")
        print(f"    Frequency: f = {1/period:.3f}")
    else:
        print(f"    No oscillation detected - system at fixed point")
    
    # Step 2: Compute Floquet exponents
    print(f"\n  Step 2: Computing Floquet exponents...")
    floquet_exponents = compute_floquet_exponents(W, trajectory, times, period, tau, gain)
    largest_floquet = floquet_exponents[0] if len(floquet_exponents) > 0 else 0.0
    
    print(f"    Largest Floquet exponent: mu_1 = {largest_floquet:.4f}")
    if largest_floquet < 0:
        print(f"    Limit cycle is STABLE")
    elif abs(largest_floquet) < 1e-6:
        print(f"    Marginal stability (phase mode)")
    else:
        print(f"    Limit cycle is UNSTABLE")
    
    # Step 3: Compute phase-dependent gamma
    print(f"\n  Step 3: Computing phase-dependent spectral gap...")
    gamma_values = []
    for i in range(0, len(trajectory), max(1, len(trajectory) // 20)):
        gamma_i = compute_instantaneous_gamma(trajectory[i], W, tau, gain)
        gamma_values.append(gamma_i)
    
    gamma_mean = np.mean(gamma_values)
    gamma_min = np.min(gamma_values)
    gamma_max = np.max(gamma_values)
    
    print(f"    gamma_mean = {gamma_mean:.4f}")
    print(f"    gamma_min = {gamma_min:.4f} (bottleneck phase)")
    print(f"    gamma_max = {gamma_max:.4f} (fast phase)")
    
    # Step 4: Path-averaged defect
    print(f"\n  Step 4: Computing path-averaged defect...")
    eps_bar, eps_t = compute_path_averaged_defect(W, trajectory, times, k=2, gain=gain)
    print(f"    eps_bar = {eps_bar:.4f}")
    
    # Step 5: Nonlinear validity horizon
    T_star_floquet = 1.0 / abs(largest_floquet) if abs(largest_floquet) > 1e-6 else float('inf')
    print(f"\n  Step 5: Validity horizon from Floquet:")
    print(f"    T*_Floquet = 1/|mu_1| = {T_star_floquet:.2f}")
    
    # Step 6: Linearity comparison
    print(f"\n  Step 6: Comparison with linear analysis:")
    if linear_gamma is not None:
        linearity_ratio = abs(linear_gamma / largest_floquet) if abs(largest_floquet) > 1e-6 else float('inf')
        print(f"    gamma_linear = {linear_gamma:.4f}")
        print(f"    gamma_linear / |mu_1| = {linearity_ratio:.2f}")
        if abs(linearity_ratio - 1.0) < 0.1:
            print(f"    System is APPROXIMATELY LINEAR")
        else:
            print(f"    System is GENUINELY NONLINEAR")
    else:
        linearity_ratio = 1.0
        print(f"    (No linear comparison provided)")
    
    if linear_epsilon is not None:
        print(f"    eps_linear = {linear_epsilon:.4f}")
        print(f"    eps_path / eps_linear = {eps_bar / linear_epsilon:.2f}" if linear_epsilon > 0 else "")
    
    # Build profile
    profile = NonlinearSGCProfile(
        W=W,
        n=n,
        sigmoid_gain=gain,
        tau=tau,
        gamma_linear=linear_gamma if linear_gamma is not None else 0.0,
        epsilon_linear=linear_epsilon if linear_epsilon is not None else 0.0,
        floquet_exponents=floquet_exponents,
        floquet_period=period,
        largest_floquet=largest_floquet,
        epsilon_path=eps_bar,
        gamma_mean=gamma_mean,
        gamma_min=gamma_min,
        gamma_max=gamma_max,
        T_star_floquet=T_star_floquet,
        trajectory=trajectory,
        times=times,
        linearity_ratio=linearity_ratio,
    )
    
    return profile


def scan_nonlinearity(W: np.ndarray, gains: List[float],
                      tau: float = 1.0,
                      linear_gamma: float = None,
                      linear_epsilon: float = None) -> Dict[str, List[float]]:
    """
    Scan how SGC quantities change with nonlinearity parameter.
    
    This is the key experimental test: as gain increases from 0 (linear)
    to large (highly nonlinear), epsilon should change systematically.
    
    Parameters:
        W: Connectivity matrix
        gains: List of sigmoid gain values to test
        tau: Time constant
        linear_gamma: Linear spectral gap for comparison
        linear_epsilon: Linear defect for comparison
    
    Returns:
        results: Dictionary with arrays for each quantity vs gain
    """
    results = {
        'gain': [],
        'epsilon_path': [],
        'gamma_mean': [],
        'largest_floquet': [],
        'period': [],
        'linearity_ratio': [],
    }
    
    print(f"\n  NONLINEARITY SCAN")
    print(f"  " + "="*60)
    print(f"  Testing gains: {gains}")
    
    for gain in gains:
        print(f"\n  --- Gain = {gain} ---")
        profile = nonlinear_sgc_analysis(W, tau=tau, gain=gain,
                                          linear_gamma=linear_gamma,
                                          linear_epsilon=linear_epsilon)
        
        results['gain'].append(gain)
        results['epsilon_path'].append(profile.epsilon_path)
        results['gamma_mean'].append(profile.gamma_mean)
        results['largest_floquet'].append(profile.largest_floquet)
        results['period'].append(profile.floquet_period)
        results['linearity_ratio'].append(profile.linearity_ratio)
    
    return results


# ============================================================================
# THEOREM FORMALIZATION: Nonlinear Emergence Equivalence
# ============================================================================

"""
THEOREM: Nonlinear Emergence Equivalence (CONJECTURE)

For a nonlinear dynamical system dp/dt = f(p) with a stable limit cycle C:

    (a) P*(p) minimizes instantaneous defect eps(p, P) at every p in C
        
    <=>
    
    (b) The slow manifold foliation is thermodynamically optimal:
        The projection onto tangent space of C minimizes entropy production
        
    <=>
    
    (c) The limit cycle is a minimum free energy path:
        C = argmin_{gamma} integral_{gamma} (entropy_production + kinetic_energy) ds

This generalizes the linear emergence_equivalence theorem from src/SGC/Core.lean
to nonlinear systems on limit cycles.

PROOF SKETCH (not yet formalized):

(a) => (b): 
    If P*(p) minimizes defect at each p, then the coarse-graining captures
    the slow dynamics. The slow manifold is tangent to P* at each point,
    so the foliation induced by P*(p) is the slow manifold foliation.

(b) => (c):
    Thermodynamic optimality of the slow manifold implies that the
    projected dynamics minimize entropy production. By the Onsager-Machlup
    principle, this is equivalent to minimizing the action functional,
    which gives a minimum free energy path.

(c) => (a):
    If C is a minimum free energy path, then small perturbations
    from C decay quickly (Floquet stability). This means the
    defect from coarse-graining is small at each point on C.

STATUS: CONJECTURE - requires formal proof in Lean 4
"""
