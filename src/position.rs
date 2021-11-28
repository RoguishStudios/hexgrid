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

use crate::Float;

/// Fractional Position on 2d hexagonal grid
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, Clone, Eq, PartialEq, Debug, Ord, PartialOrd)]
pub struct Position<F: Float = f32> {
    /// `x` coordinate
    pub x: F,
    /// `y` coordinate
    pub y: F,
}
