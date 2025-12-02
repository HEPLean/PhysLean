/-
Copyright (c) 2025 Shlok Vaibhav Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlok Vaibhav Singh
-/
/-!
# Sliding Pendulum
### Tag: LnL_1.5.2
## Source
* Textbook: Landau and Lifshitz, Mechanics, 3rd Edition
* Chapter: 1 The Equations of motion
* Section: 5 The Lagrangian for a system of particles
* Problem 2: Sliding Pendulum

## Description
A simple pendulum of mass $m_2$ attached to a mass $m_1$ as its point of support via a string of
length $l$.
The mass $m_1$ is free to move horizontally. The lagrangian of the system is to be found.

## Solution
First, the constraints are identified:
$$
\begin{align}
y_1 &= 0 \\
(x_2 - x_1)^2 + (y_2-y_1)^2 &= l^2
\end{align}
$$
So that $x_2-x_1 = l \sin(\phi)$ and $y_2-y_1 = y_2 = - l \cos(φ)$ with generalized coordinate, $φ$,
being the angle the string makes with vertical.

The Lagrangian is obtained as:
$$\mathcal{L} = T_1 + T_2 - V_1 - V_2$$ where
* Kinetic energy of $m_1$   :    $\quad T_1 = \frac{1}{2} m_1 \dot{x}_1^2 $
* Potential energy of $m_1$:     $\enspace V_1 = 0$
* Kinetic energy of $m_2$  :     $\quad T_2 = \frac{1}{2} m_2 (\dot{x}_2^2 + \dot{y}_2^2)
= \frac{1}{2} m_2 [l^2 \dot{φ}^2 + \dot{x}_1^2 + 2 l \dot{φ} \dot{x}_1 \cos(φ)]$
* Potential energy of $m_2$:     $\enspace V_2 = m_2 g y_2 = - m_2 g l \cos(φ)$

So that
$$\mathcal{L} = \frac{1}{2} (m_1 + m_2) \dot{x}_1^2 + \frac{1}{2} m_2 (l^2 \dot{φ}^2 +
2 l \dot{φ} \dot{x}_1 \cos(φ)) + m_2 g l \cos(φ)$$

-/

namespace ClassicalMechanics

end ClassicalMechanics
