/-
Copyright (c) 2025 Shlok Vaibhav Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlok Vaibhav Singh
-/
/-! {LnL_1.5.1}
Source:
Textbook: Landau and Lifshitz, Mechanics, 3rd Edition
Chapter 1 The Equations of motion
Section 5 The Lagrangian for a system of particles
Problem 1: Coplanar Double Pendulum

Description: This problem involves:
a) identifying the appropriate Degrees of Freedom or generalized coordinates
and their relation to cartesian coordinates
b) and using them to write down the Lagrangian for

a coplanar double pendulum made up of two point masses m1 and m2. m1 is attached to the
pivot and m2 is attached to m1 via strings of length l1 and l2 respectively.

Solution:
a) The cartesian coordinates (x1,y1) (For m1) and (x2,y2) (for m2) can be expressed with the
two angles made by the strings with vertical φ1 and φ2 and two constraints on distance between
m1 and pivot and m2 and m1:
x1 = l1 sin(φ1)
y1 = - l1 cos(φ1)
x2 = l1 sin(φ1) + l2 sin(φ2)
y2 = - l1 cos(φ1) - l2 cos(φ2)

b) The Lagrangian is obtained by writing down the kinetic and potential energies
first in terms of cartesian coordinates and their time derivates and then substituting
the coordinates and derivatives with transformations obtained in a) :

L = T1 + T2 - V1 - V2 where
T1 = 1/2 m1 (x1_dot^2 + y1_dot^2) = 1/2 m1 l1^2 φ1_dot^2 (Kinetic energy of m1)
Here and in next problems, _dot denotes time derivate
V1 = m1 g y1 = - m1 g l1 cos(φ1) (Potential energy of m1)
T2 = 1/2 m2 (x2_dot^2 + y2_dot^2)
= 1/2 m2 [l1^2 φ1_dot^2 + l2^2 φ2_dot^2 + 2 l1 l2 φ1_dot φ2_dot cos(φ1 - φ2)] (Kinetic energy of m2)
V2 = m2 g y2 = - m2 g [l1 cos(φ1) + l2 cos(φ2)] (Potential energy of m2)

so that the Lagrangian becomes:
L = 1/2 (m1 + m2) l1^2 φ1_dot^2 + 1/2 m2 l2^2 φ2_dot^2 + m2 l1 l2 φ1_dot φ2_dot cos(φ1 - φ2)
    + (m1 + m2) g l1 cos(φ1) + m2 g l2 cos(φ2)
-/
