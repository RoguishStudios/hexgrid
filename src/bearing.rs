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

use crate::{Angle, Coordinate, Direction, Integer};

/// Bearing on 2d hexagonal grid (Coordinate + Direction)
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub struct Bearing<I: Integer = i32> {
    /// Coordinate
    pub coordinate: Coordinate<I>,
    /// `y` coordinate
    pub direction: Direction,
}

impl<I: Integer> Bearing<I> {
    /// Create a new Position
    pub fn new(coordinate: Coordinate<I>, direction: Direction) -> Bearing<I> {
        Bearing {
            coordinate,
            direction,
        }
    }
}

impl<I: Integer> std::ops::Add<Coordinate<I>> for Bearing<I> {
    type Output = Bearing<I>;

    fn add(self, coordinate: Coordinate<I>) -> Bearing<I> {
        Bearing {
            coordinate: self.coordinate + coordinate,
            direction: self.direction,
        }
    }
}

impl<I: Integer> std::ops::Add<Angle> for Bearing<I> {
    type Output = Bearing<I>;

    fn add(self, angle: Angle) -> Bearing<I> {
        Bearing {
            coordinate: self.coordinate,
            direction: self.direction + angle,
        }
    }
}

impl<I: Integer> std::ops::Sub<Coordinate<I>> for Bearing<I> {
    type Output = Bearing<I>;

    fn sub(self, coordinate: Coordinate<I>) -> Bearing<I> {
        Bearing {
            coordinate: self.coordinate - coordinate,
            direction: self.direction,
        }
    }
}

impl From<Direction> for Bearing {
    fn from(direction: Direction) -> Self {
        Bearing {
            coordinate: Coordinate::default(),
            direction,
        }
    }
}
