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

use crate::{Coordinate, Integer, Ring, Spin};

/// Iterates through all hexes in a hexagonal shaped spiral pattern.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub struct Spiral<I: Integer> {
    origin: Coordinate<I>,
    radius: I,
    ring_iter: Ring<I>,
    spin: Spin,
}

impl<I: Integer> Spiral<I> {
    pub(crate) fn new(origin: &Coordinate<I>, radius: I, spin: Spin) -> Spiral<I> {
        Spiral {
            origin: origin.clone(),
            ring_iter: origin.ring_iter(I::zero(), spin),
            radius,
            spin,
        }
    }
    /// Get maximum Radius of Spiral
    pub fn radius(&self) -> I {
        self.radius
    }
    /// Get current Radius layer of Spiral
    pub fn layer(&self) -> I {
        self.ring_iter.radius()
    }
}

impl<I: Integer> Iterator for Spiral<I> {
    type Item = Coordinate<I>;

    fn next(&mut self) -> Option<Self::Item> {
        let res = self.ring_iter.next();
        if res.is_some() {
            res
        } else if self.ring_iter.radius() < self.radius {
            self.ring_iter = self
                .origin
                .ring_iter(self.ring_iter.radius() + I::one(), self.spin);
            self.ring_iter.next()
        } else {
            None
        }
    }
}

impl<I: Integer> std::iter::FusedIterator for Spiral<I> {}
impl<I: Integer> std::iter::ExactSizeIterator for Spiral<I> {}
