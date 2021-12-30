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

use crate::{Angle, Bearing, Coordinate, Integer, Spin};
use std::cmp::max;

/// Iterates in a ring around an origin at provided radius.
/// ### Ring Iteration Pattern:
/// ```rust
/// use hexgrid::{Coordinate, Spin, Direction};
///
/// for location in Coordinate::from_axial(0, 0).ring_iter(5, Spin::CW(Direction::YZ)) {
///     assert_eq!(location.distance(Coordinate::from_axial(0,0)), 5);
/// }
/// ```
#[doc = include_str!("ring.svg")]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub struct Ring<I: Integer> {
    origin: Coordinate<I>,
    current: Bearing<I>,
    step_angle: Angle,
    r: I,
    ii: I,
    jj: I,
    fuse: bool,
}

impl<I: Integer> Ring<I> {
    pub(crate) fn new(origin: &Coordinate<I>, radius: I, spin: Spin) -> Ring<I> {
        let (start_angle, step_angle, start_dir) = match spin {
            Spin::CW(d) => (
                if radius >= I::zero() {
                    Angle::RightBackward
                } else {
                    Angle::LeftForward
                },
                Angle::RightForward,
                d,
            ),
            Spin::CCW(d) => (
                if radius >= I::zero() {
                    Angle::LeftBackward
                } else {
                    Angle::RightForward
                },
                Angle::LeftForward,
                d,
            ),
        };

        let cur_coord: Coordinate<I> = *origin + Coordinate::from(start_dir).scale(radius);
        let cur_dir = start_dir + start_angle;

        Ring {
            origin: origin.clone(),
            current: Bearing::new(cur_coord, cur_dir),
            step_angle,
            r: I::abs(&radius),
            ii: I::zero(),
            jj: I::zero(),
            fuse: false,
        }
    }
    /// Get Radius of the `Ring`
    pub fn radius(&self) -> I {
        self.r
    }
}

impl<I: Integer> Iterator for Ring<I> {
    type Item = Coordinate<I>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.fuse {
            return None;
        }
        if self.r.is_zero() {
            self.fuse = true;
            return Some(self.origin);
        }

        if self.jj >= self.r.abs() {
            self.ii += I::one();
            if self.ii >= I::from_u8(6).unwrap() {
                self.fuse = true;
                return None;
            }
            self.current.direction = self.current.direction + self.step_angle;
            self.jj = I::zero();
        }
        self.jj += I::one();

        let ret = Some(self.current.coordinate);
        let current_direction_offset: Coordinate<_> = self.current.direction.into();
        self.current.coordinate = self.current.coordinate + current_direction_offset;

        ret
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.fuse {
            return (0, Some(0));
        }
        let total_size: usize = if self.r == I::zero() {
            1
        } else {
            I::to_usize(&(self.r * I::from_u8(6).unwrap())).unwrap()
        };
        let past: usize =
            num::ToPrimitive::to_usize(max(&I::zero(), &(self.jj + self.ii * self.r))).unwrap();
        (total_size - past, Some(total_size - past))
    }
}

impl<I: Integer> std::iter::FusedIterator for Ring<I> {}
impl<I: Integer> std::iter::ExactSizeIterator for Ring<I> {}
