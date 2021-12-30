//
// Copyright 2021 Hans W. Uhlig. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// See LICENSE file for more information
//

use crate::{Bearing, Coordinate, Direction, Float, Integer, Spacing};

/// Fractional Position on 2d hexagonal grid
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, Clone, Eq, PartialEq, Debug, Ord, PartialOrd)]
pub struct Position<F: Float = f32> {
    /// Axial `q` coordinate
    pub q: F,
    /// Axial `r` coordinate
    pub r: F,
}

impl<F: Float> Position<F> {
    /// Create new Coordinate from `q` and `r` axial components.
    ///
    /// See [Hex Coordinates](https://www.redblobgames.com/grids/hexagons/#coordinates).
    pub fn from_axial(q: F, r: F) -> Position<F> {
        Position { q, r }
    }

    /// Create new Coordinate from `x`, `y`, and `z` cubic components.
    ///
    /// See [Hex Coordinates](https://www.redblobgames.com/grids/hexagons/#coordinates).
    pub fn from_cubic(x: F, y: F, z: F) -> Position<F> {
        assert!(x + y + z == F::zero());
        Position { q: x, r: z }
    }

    /// Create Position from Hex Coordinate.
    pub fn from_coordinate<I: Integer>(coordinate: Coordinate<I>) -> Position<F> {
        Position {
            q: F::from(coordinate.q).unwrap(),
            r: F::from(coordinate.r).unwrap(),
        }
    }

    /// Convert a cartesian point into a hex position. The origin of the cartesian space is the
    /// center of the hex at (0,0) in hex coordinates.
    ///
    /// See [Screen to Hex](https://www.redblobgames.com/grids/hexagons/implementation.html#pixel-to-hex).
    pub fn from_cartesian(x: F, y: F, spacing: Spacing<F>) -> Position<F> {
        let f2: F = F::from(2).unwrap();
        let f3: F = F::from(3).unwrap();
        let f3s: F = f3.sqrt();

        match spacing {
            Spacing::PointyTop(size) => Position {
                q: (x * f3s / f3 - y / f3) / size,
                r: (y * f2 / f3) / size,
            },
            Spacing::FlatTop(size) => Position {
                q: (x * f2 / f3) / size,
                r: (-x / f3 + f3s / f3 * y) / size,
            },
        }
    }

    /// Convert Position into Cartesian coordinates with their origin at (0, 0).
    ///
    /// See [Hex to Pixel](https://www.redblobgames.com/grids/hexagons/#hex-to-pixel).
    pub fn into_cartesian(&self, spacing: Spacing<F>) -> (F, F) {
        let f2: F = F::from(2).unwrap();
        let f3: F = F::from(3).unwrap();
        let f3s: F = f3.sqrt();
        match spacing {
            Spacing::FlatTop(size) => (
                size * (f3 / f2 * self.q),
                size * (f3s / f2 * self.q + f3s * self.r),
            ),
            Spacing::PointyTop(size) => (
                size * (f3s * self.q + f3s / f2 * self.r),
                size * (f3 / f2 * self.r),
            ),
        }
    }

    /// Cubic Hex `X` coordinate
    pub fn x(&self) -> F {
        self.q
    }

    /// Cubic Hex `Y` coordinate
    pub fn y(&self) -> F {
        F::zero() - self.q - self.r
    }

    /// Cubic Hex `Z` coordinate
    pub fn z(&self) -> F {
        self.r
    }

    /// Distance from Origin
    pub fn length(&self) -> F {
        (self.x().abs() + self.y().abs() + self.z().abs()) / F::from_f64(2.0).unwrap()
    }

    /// Distance between two Positions in Hex Space
    pub fn distance(&self, position: Position<F>) -> F {
        (self.x() - position.x()).abs()
            + (self.y() - position.y()).abs()
            + (self.z() - position.z()).abs() / F::from_f64(2.0).unwrap()
    }

    /// Round Position into the nearest Coordinate
    ///
    /// See [Coordinate::from_position](crate::Coordinate::from_position).
    /// See [Hex Rounding](https://www.redblobgames.com/grids/hexagons/implementation.html#rounding).
    pub fn into_coordinate<I: Integer>(&self) -> Coordinate<I> {
        Coordinate::from_position(*self)
    }
}

impl<F: Float> From<(F, F)> for Position<F> {
    fn from(qr: (F, F)) -> Self {
        Position::from_axial(qr.0, qr.1)
    }
}

impl<F: Float> From<(F, F, F)> for Position<F> {
    fn from(xyz: (F, F, F)) -> Self {
        Position::from_cubic(xyz.0, xyz.1, xyz.2)
    }
}

impl<F: Float, I: Integer> From<Coordinate<I>> for Position<F> {
    fn from(coordinate: Coordinate<I>) -> Self {
        Position::from_coordinate(coordinate)
    }
}

impl<F: Float, I: Integer> From<Bearing<I>> for Position<F> {
    fn from(bearing: Bearing<I>) -> Self {
        bearing.coordinate.into_position()
    }
}

impl<F: Float> From<Direction> for Position<F> {
    fn from(direction: Direction) -> Self {
        let (q, r) = match direction {
            Direction::YZ => (0.0, 1.0),
            Direction::XZ => (1.0, 0.0),
            Direction::XY => (1.0, -1.0),
            Direction::ZY => (0.0, -1.0),
            Direction::ZX => (-1.0, 0.0),
            Direction::YX => (-1.0, 1.0),
        };

        Position {
            q: F::from(q).unwrap(),
            r: F::from(r).unwrap(),
        }
    }
}

impl<F: Float, T: Into<Position<F>>> std::ops::Add<T> for Position<F> {
    type Output = Position<F>;

    fn add(self, rhs: T) -> Self {
        let p: Position<_> = rhs.into();

        Position {
            q: self.q + p.q,
            r: self.r + p.r,
        }
    }
}

impl<F: Float, T: Into<Position<F>>> std::ops::Sub<T> for Position<F> {
    type Output = Position<F>;

    fn sub(self, rhs: T) -> Self {
        let p: Position<_> = rhs.into();

        Position {
            q: self.q - p.q,
            r: self.r - p.r,
        }
    }
}

impl<F: Float> std::ops::Mul<F> for Position<F> {
    type Output = Position<F>;

    fn mul(self, rhs: F) -> Self {
        Position {
            q: self.q * rhs,
            r: self.r * rhs,
        }
    }
}

impl<F: Float> std::ops::Neg for Position<F> {
    type Output = Position<F>;

    fn neg(self) -> Self {
        Position {
            q: -self.q,
            r: -self.r,
        }
    }
}
