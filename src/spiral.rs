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

use crate::{Angle, Coordinate, Direction, Integer, Spin};
use std::usize;

/// Iterates through all hexes in a hexagonal shaped spiral pattern.
#[doc = include_str!("spiral.svg")]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub struct Spiral<I: Integer> {
    origin_coordinate: Coordinate<I>,
    current_coordinate: Coordinate<I>,
    current_direction: Direction,
    start_direction: Direction,
    step_angle: Angle,
    radius: I,
    layer: I,
    idx: I,
    ii: I,
    jj: I,
    fuse: bool,
}

impl<I: Integer> Spiral<I> {
    pub(crate) fn new(origin: Coordinate<I>, radius: I, spin: Spin) -> Spiral<I> {
        let (start_angle, step_angle, start_direction) = match spin {
            Spin::CW(direction) => (Angle::RightBackward, Angle::RightForward, direction),
            Spin::CCW(direction) => (Angle::LeftBackward, Angle::LeftForward, direction),
        };

        Spiral {
            origin_coordinate: origin,
            current_coordinate: origin + start_direction,
            current_direction: start_direction + start_angle,
            start_direction,
            step_angle,
            layer: I::zero(),
            idx: I::zero(),
            ii: I::zero(),
            jj: I::zero(),
            fuse: false,
            radius,
        }
    }
    /// Get current layer of the `Spiral`
    pub fn layer(&self) -> I {
        self.layer
    }
    /// Get final radius of the `Spiral`
    pub fn radius(&self) -> I {
        self.radius
    }
}

impl<I: Integer> Iterator for Spiral<I> {
    type Item = Coordinate<I>;

    fn next(&mut self) -> Option<Self::Item> {
        // Iterator has fused and finished the Spiral, will return None forevermore.
        if self.fuse {
            return None;
        }

        // If current layer is zero, return origin.
        // If radius is also zero, then fuse.
        if self.layer.is_zero() {
            if self.radius.is_zero() {
                self.fuse = true;
            } else {
                self.layer += I::one();
                self.idx += I::one();
            }
            return Some(self.origin_coordinate);
        }

        // ii is the current side relative to the starting location. 0-5
        // jj is the position on the current side.
        // if jj > current layer radius. increment side and rotate
        // if ii > 6, then increment radius and start over.
        if self.jj >= self.layer.abs() {
            // Increment current side
            self.ii += I::one();
            // if side > 6, increment layer
            if self.ii >= I::from_u8(6).unwrap() {
                // If layer is equal or greater than radius, fuse
                if self.layer >= self.radius {
                    self.fuse = true;
                    return None;
                }
                self.layer += I::one();
                self.ii = I::zero();
                self.current_coordinate = Coordinate::from(self.start_direction).scale(self.layer);
            }
            // Rotate Direction by Step Angle, and set side position to zero
            self.current_direction = self.current_direction + self.step_angle;
            self.jj = I::zero();
        }
        // Increment Side Position
        self.jj += I::one();
        // Increment index. TODO: Remove
        self.idx += I::one();

        let ret = Some(self.current_coordinate);
        let current_direction_offset: Coordinate<_> = self.current_direction.into();
        self.current_coordinate = self.current_coordinate + current_direction_offset;

        ret
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.fuse {
            return (0, Some(0));
        }

        let total_size: usize = (0..=self.radius.to_usize().unwrap())
            .map(|layer| if layer == 0 { 1 } else { layer * 6 })
            .sum();
        let remaining = total_size - self.idx.to_usize().unwrap();

        (remaining, Some(remaining))
    }
}

impl<I: Integer> std::iter::FusedIterator for Spiral<I> {}
impl<I: Integer> std::iter::ExactSizeIterator for Spiral<I> {}
