/-
Copyright (c) 2025 Shlok Vaibhav Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlok Vaibhav Singh
-/
/-   {LnL_1.5.2}
Source:
Textbook: Landau and Lifshitz, Mechanics, 3rd Edition
Chapter 1 The Equations of motion
Section 5 The Lagrangian for a system of particles
Problem 2: Sliding Pendulum

Description:
A simple pendulum of mass m2 attached to a mass m1 as its point of support via a string of length l.
The mass m1 is free to move horizontally. The lagrangiian of the system is to be found.

Solution:
First, the constraints are identified:
y1 = 0
(x2 - x1)^2 + (y2-y1)^2 = l^2

So that x2-x1 = l sin(φ) and y2-y1 = y2 = - l cos(φ) with the generalized coordinate, φ,
being the angle the string makes with vertical.

The Lagrangian is obtained as:
L = T1 + T2 - V1 - V2 where
T1 = 1/2 m1 x1_dot^2  (Kinetic energy of m1)
V1 = 0
T2 = 1/2 m2 (x2_dot^2 + y2_dot^2) = 1/2 m2 [l^2 φ_dot^2 + x1_dot^2 + 2 l φ_dot x1_dot cos(φ)]
(Kinetic energy of m2)
V2 = m2 g y2 = - m2 g l cos(φ)                     (Potential energy of m2)
So that
L = 1/2 (m1 + m2) x1_dot^2 + 1/2 m2 (l^2 φ_dot^2 + 2 l φ_dot x1_dot cos(φ)) + m2 g l cos(φ)

-/
