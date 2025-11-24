/-   {LnL_1.5.3}
Source:
Textbook: Landau and Lifshitz, Mechanics, 3rd Edition
Chapter 1 The Equations of motion
Section 5 The Lagrangian for a system of particles
Problem 3: Pendulum with a moving suspension point

In all three cases described below, the point of support moves in the same plane as the pendulum as
per a given function of time. The lagrangian of the pendulum is to be found.

Part a)
Description: The pendulum moves uniformally in a vertical circle of radius a and angular velocity γ.
Solution:
The coordinates of m can be expressed as:
x = a cos(γ t) + l sin(φ)
y = a sin(γ t) - l cos(φ)       (where generalized coordinate, φ, is the angle the string makes
with vertical, γ is angle with horizontal)

L = T - V where
T = 1/2 m (x_dot^2 + y_dot^2) = 1/2 m [l^2 φ_dot^2 + 2 a l γ sin(φ - γ t) φ_dot + a^2 γ^2]
V = m g y = m g [a sin(γ t) - l cos(φ)]

We can ignore the constant term 1/2 m a^2 γ^2 in T as it does not affect the equations of motion.
Like wise, m g a sin(γ t) in V can be ignored since its contribution to the action is constant
Let us note that the total derivate of a l cos(φ - γ t) is:
d/dt [a l cos(φ - γ t)] = - a l sin(φ - γ t) φ_dot + a l γ sin(φ - γ t)
Rearraging the terms, the lagrangian can be written as:
L = 1/2 m l^2 φ_dot^2 + m a l γ^2 sin(φ - γ t)  + m g l cos(φ) - m γ d/dt [a l cos(φ - γ t)]

Since lagrangians differing by a total time derivate lead to the same equations of motion
we can ignore the last term. So that the final lagrangian becomes:
L = 1/2 m l^2 φ_dot^2 + m a l γ^2 sin(φ - γ t)  + m g l cos(φ)


Part b)
Description: The point of support oscillates horizontally according to the law x = a cos(γ t).
Solution:
The coordinates of m can be expressed as:
x = a cos(γ t) + l sin(φ)
y = - l cos(φ)       (where generalized coordinate, φ, is the angle the string makes with vertical)

so that x_dot = - a γ sin(γ t) + l φ_dot cos(φ) and y_dot = l φ_dot sin(φ)
L = T - V where
T = 1/2 m (x_dot^2 + y_dot^2)
= 1/2 m [l^2 φ_dot^2 + a^2 γ^2 sin^2(γ t) - 2 a l γ sin(γ t) φ_dot cos(φ)]
V = m g y = - m g l cos(φ)
We can ignore the constant term 1/2 m a^2 γ^2 sin^2(γ t) in T again
The derivative of sin(φ) sin(γ t) is:
d/dt [sin(φ) sin(γ t)] = φ_dot cos(φ) sin(γ t) + γ sin(φ) cos(γ t)
substituting this in the lagrangian, we get:
L = 1/2 m l^2 φ_dot^2 + m a l γ^2 sin(φ) cos(γ t) + m g l cos(φ) - m a l γ d/dt [sin(φ) sin(γ t)]

Ignoring the total time derivate term, the final lagrangian becomes:
L = 1/2 m l^2 φ_dot^2 + m a l γ^2 sin(φ) cos(γ t) + m g l cos(φ)

Part c)
Description: The point of support oscillates vertically according to the law y = a cos(γ t).
Solution:
The coordinates of m can be expressed as:
x = l sin(φ)
y = a cos(γ t) - l cos(φ)  (where generalized coordinate, φ, is angle string makes with vertical)
L = T - V where
T = 1/2 m (x_dot^2 + y_dot^2)
= 1/2 m [l^2 φ_dot^2 + a^2 γ^2 sin^2(γ t) - 2 a l γ sin(γ t) φ_dot sin(φ)]
V = m g y = m g [a cos(γ t) - l cos(φ)]
We can ignore the constant term 1/2 m a^2 γ^2 sin^2(γ t) in T as it does not lead to variation.
Likewise, m g a cos(γ t) in V can be ignored since its contribution to the action  is constant
The time derivative of cos(φ) sin(γ t) is:
d/dt [cos(φ) sin(γ t)] = - φ_dot sin(φ) sin(γ t) + γ cos(φ) cos(γ t)
substituting this in the lagrangian, we get:
L = 1/2 m l^2 φ_dot^2 + m g l cos(φ) - m a l γ^2  cos(φ) cos(γ t) + m a l γ d/dt [cos(φ) cos(γ t)]
Ignoring the total time derivate term, the final lagrangian becomes:
L = 1/2 m l^2 φ_dot^2 + m g l cos(φ) - m a l γ^2  cos(φ) cos(γ t)
-/
