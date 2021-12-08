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

use crate::spin::Spin;
use crate::{Angle, Bearing, Float, Integer};

/// Direction on a hexagonal map
///
/// See [Coordinate](crate::Coordinate) for graph with directions.
///
/// Naming convention: increasing coordinate for a given direction is first
/// decreasing is second. The missing coordinate is unaffected by a move in
/// a given direction.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub enum Direction {
    /// +Y -Z
    YZ,
    /// -Z +X
    XZ,
    /// +X -Y
    XY,
    /// -Y +Z
    ZY,
    /// +Z -X
    ZX,
    /// -X +Y
    YX,
}

impl Direction {
    /// Static array of all directions
    ///
    /// ```
    /// use hexgrid::Direction;
    ///
    /// assert_eq!(Direction::all().len(), 6);
    /// ```
    pub fn all() -> &'static [Direction; 6] {
        &[
            Direction::YZ,
            Direction::XZ,
            Direction::XY,
            Direction::ZY,
            Direction::ZX,
            Direction::YX,
        ]
    }

    /// Return a vector of an arc including Directions `steps` away from the original Direction both
    /// sides from left to right.
    ///
    /// ```
    /// use hexgrid::{Direction};
    /// use hexgrid::Angle::*;
    ///
    /// for &d in Direction::all() {
    ///     assert_eq!(d.arc(0), vec!(d));
    ///     assert_eq!(d.arc(1), vec!(d + LeftForward, d, d + RightForward));
    ///     assert_eq!(d.arc(2), vec!(d + LeftBackward, d + LeftForward, d, d + RightForward, d + RightBackward));
    ///     assert_eq!(d.arc(3), vec!(d + LeftBackward, d + LeftForward, d, d + RightForward, d + RightBackward, d + Backward));
    /// }
    /// ```
    pub fn arc(&self, steps: u8) -> Vec<Direction> {
        match steps {
            0 => vec![*self],
            1 => vec![
                *self + Angle::LeftForward,
                *self,
                *self + Angle::RightForward,
            ],
            2 => vec![
                *self + Angle::LeftBackward,
                *self + Angle::LeftForward,
                *self,
                *self + Angle::RightForward,
                *self + Angle::RightBackward,
            ],
            _ => vec![
                *self + Angle::LeftBackward,
                *self + Angle::LeftForward,
                *self,
                *self + Angle::RightForward,
                *self + Angle::RightBackward,
                *self + Angle::Backward,
            ],
        }
    }

    /// Create Direction from integer in [0, 6) range
    ///
    /// This should probably be internal
    pub fn from_int<I: Integer>(i: I) -> Direction {
        match i.mod_floor(&I::from_i8(6).unwrap()).to_u8().unwrap() {
            0 => Direction::YZ,
            1 => Direction::XZ,
            2 => Direction::XY,
            3 => Direction::ZY,
            4 => Direction::ZX,
            5 => Direction::YX,
            _ => panic!(),
        }
    }

    /// Convert to integer in [0, 6) range
    ///
    /// This should probably be internal
    pub fn to_int<I: Integer>(&self) -> I {
        I::from_u8(*self as u8).unwrap()
    }

    /// Convert to angle for pointy-topped map, in radians, grows clockwise, 0.0 points up
    pub fn to_radians_pointy<T: Float>(&self) -> T {
        use std::f64::consts::PI;
        T::from(match *self {
            Direction::YZ => PI * (5.5 / 3.0),
            Direction::XZ => PI * (0.5 / 3.0),
            Direction::XY => PI * (1.5 / 3.0),
            Direction::ZY => PI * (2.5 / 3.0),
            Direction::ZX => PI * (3.5 / 3.0),
            Direction::YX => PI * (4.5 / 3.0),
        })
        .unwrap()
    }

    /// Convert to angle for flat-topped map, in radians, grows clockwise, 0.0 points up
    pub fn to_radians_flat<T: Float>(&self) -> T {
        self.to_radians_pointy::<T>() + T::from(std::f64::consts::PI * (0.5 / 3.0)).unwrap()
    }
}

impl<T: Into<Direction>> std::ops::Sub<T> for Direction {
    type Output = Angle;

    fn sub(self, c: T) -> Angle {
        let c: Direction = c.into();

        Angle::from_int::<i8>(self.to_int::<i8>() - c.to_int::<i8>())
    }
}

impl From<Spin> for Direction {
    fn from(spin: Spin) -> Self {
        match spin {
            Spin::CW(d) => d,
            Spin::CCW(d) => d,
        }
    }
}

impl<I: Integer> From<Bearing<I>> for Direction {
    fn from(bearing: Bearing<I>) -> Self {
        bearing.direction
    }
}

impl std::ops::Neg for Direction {
    type Output = Direction;

    fn neg(self) -> Direction {
        match self {
            Direction::YZ => Direction::ZY,
            Direction::XZ => Direction::ZX,
            Direction::XY => Direction::YX,
            Direction::ZY => Direction::YZ,
            Direction::ZX => Direction::XZ,
            Direction::YX => Direction::XY,
        }
    }
}

impl std::ops::Add<Angle> for Direction {
    type Output = Direction;

    fn add(self, a: Angle) -> Direction {
        Direction::from_int(self.to_int::<i8>() + a.to_int::<i8>())
    }
}

impl std::ops::Sub<Angle> for Direction {
    type Output = Direction;

    fn sub(self, a: Angle) -> Direction {
        Direction::from_int(self.to_int::<i8>() - a.to_int::<i8>())
    }
}
