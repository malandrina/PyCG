#
# Copyright (c) 2020 Vitalis Salis.
#
# Licensed to the Apache Software Foundation (ASF) under one
# or more contributor license agreements.  See the NOTICE file
# distributed with this work for additional information
# regarding copyright ownership.  The ASF licenses this file
# to you under the Apache License, Version 2.0 (the
# "License"); you may not use this file except in compliance
# with the License.  You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
# KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations
# under the License.
#
from pycg import utils
from pycg.machinery.pointers import LiteralPointer, NamePointer


class DefinitionManager(object):
    def __init__(self):
        self.defs = {}

    def create(self, ns, def_type):
        if not ns or not isinstance(ns, str):
            raise DefinitionError("Invalid namespace argument")
        if def_type not in Definition.types:
            raise DefinitionError("Invalid def type argument")
        if self.get(ns):
            raise DefinitionError("Definition already exists")

        self.defs[ns] = Definition(ns, def_type)
        return self.defs[ns]

    def assign(self, ns, defi):
        self.defs[ns] = Definition(ns, defi.get_type())
        self.defs[ns].merge(defi)

        # if it is a function def, we need to create a return pointer
        if defi.is_function_def():
            return_ns = utils.join_ns(ns, utils.constants.RETURN_NAME)
            self.defs[return_ns] = Definition(return_ns, utils.constants.NAME_DEF)
            self.defs[return_ns].get_name_pointer().add(
                utils.join_ns(defi.get_ns(), utils.constants.RETURN_NAME)
            )

        return self.defs[ns]

    def get(self, ns):
        if ns in self.defs:
            return self.defs[ns]

    def get_defs(self):
        return self.defs

    def handle_function_def(self, parent_ns, fn_name):
        full_ns = utils.join_ns(parent_ns, fn_name)
        defi = self.get(full_ns)
        if not defi:
            defi = self.create(full_ns, utils.constants.FUN_DEF)
            defi.decorator_names = set()

        return_ns = utils.join_ns(full_ns, utils.constants.RETURN_NAME)
        if not self.get(return_ns):
            self.create(return_ns, utils.constants.NAME_DEF)

        return defi

    def handle_class_def(self, parent_ns, cls_name):
        full_ns = utils.join_ns(parent_ns, cls_name)
        defi = self.get(full_ns)
        if not defi:
            defi = self.create(full_ns, utils.constants.CLS_DEF)

        return defi

    def transitive_closure(self):
        closured = {}

        def dfs(defi):
            name_pointer = defi.get_name_pointer()
            new_set = set()
            # bottom
            if closured.get(defi.get_ns(), None) is not None:
                return closured[defi.get_ns()]

            if not name_pointer.get():
                new_set.add(defi.get_ns())

            closured[defi.get_ns()] = new_set

            for name in name_pointer.get():
                if not self.defs.get(name, None):
                    continue
                items = dfs(self.defs[name])
                if not items:
                    items = set([name])
                new_set = new_set.union(items)

            closured[defi.get_ns()] = new_set
            return closured[defi.get_ns()]

        for ns, current_def in self.defs.items():
            if closured.get(current_def, None) is None:
                dfs(current_def)

        return closured

    def complete_definitions(self):
        """Complete all definitions by propagating pointer relationships.
        This is an optimized version that tracks changes and uses sets for better performance."""
        def update_pointsto_args(pointsto_args, arg, name):
            if arg == pointsto_args:
                return False

            changed = False
            # Convert to sets for faster operations
            arg_set = set(arg)

            for pointsto_arg in pointsto_args:
                # Cache definition lookup
                pointsto_def = self.defs.get(pointsto_arg)
                if not pointsto_def or pointsto_arg == name:
                    continue

                pointsto_arg_def = pointsto_def.get_name_pointer()
                if pointsto_arg_def == pointsto_args:
                    continue

                # Get existing items after we have pointsto_arg_def
                existing = set(pointsto_arg_def.get())
                # Cache definition lookup
                pointsto_def = self.defs.get(pointsto_arg)
                if not pointsto_def or pointsto_arg == name:
                    continue

                pointsto_arg_def = pointsto_def.get_name_pointer()
                if pointsto_arg_def == pointsto_args:
                    continue

                # Remove cycles efficiently using set difference
                arg_set.discard(pointsto_arg)

                # Find new items to add
                new_items = {x for x in arg_set if x in self.defs}
                new_items -= existing

                if new_items:
                    changed = True
                    for item in new_items:
                        pointsto_arg_def.add(item)

            return changed

        # Track which definitions have changed
        changed_defs = set(self.defs.keys())
        
        while changed_defs:
            new_changes = set()
            
            for ns in changed_defs:
                current_def = self.defs[ns]
                current_name_pointer = current_def.get_name_pointer()
                
                # Cache the names to avoid modification during iteration
                names = set(current_name_pointer.get())
                
                for name in names:
                    pointsto_def = self.defs.get(name)
                    if not pointsto_def or name == ns:
                        continue

                    pointsto_name_pointer = pointsto_def.get_name_pointer()
                    
                    # Process arguments more efficiently
                    for arg_name, arg in current_name_pointer.get_args().items():
                        pos = current_name_pointer.get_pos_of_name(arg_name)
                        
                        if pos is not None:
                            pointsto_args = pointsto_name_pointer.get_pos_arg(pos)
                            if not pointsto_args:
                                pointsto_name_pointer.add_pos_arg(pos, None, arg)
                                new_changes.add(name)
                                continue
                        else:
                            pointsto_args = pointsto_name_pointer.get_arg(arg_name)
                            if not pointsto_args:
                                pointsto_name_pointer.add_arg(arg_name, arg)
                                new_changes.add(name)
                                continue
                                
                        if update_pointsto_args(pointsto_args, arg, current_def.get_ns()):
                            new_changes.add(name)
                            
            # Only continue if we found new changes
            changed_defs = new_changes


class Definition(object):
    types = [
        utils.constants.FUN_DEF,
        utils.constants.MOD_DEF,
        utils.constants.NAME_DEF,
        utils.constants.CLS_DEF,
        utils.constants.EXT_DEF,
    ]

    def __init__(self, fullns, def_type):
        self.fullns = fullns
        self.points_to = {"lit": LiteralPointer(), "name": NamePointer()}
        self.def_type = def_type

    def get_type(self):
        return self.def_type

    def is_function_def(self):
        return self.def_type == utils.constants.FUN_DEF

    def is_ext_def(self):
        return self.def_type == utils.constants.EXT_DEF

    def is_callable(self):
        return self.is_function_def() or self.is_ext_def()

    def get_lit_pointer(self):
        return self.points_to["lit"]

    def get_name_pointer(self):
        return self.points_to["name"]

    def get_name(self):
        return self.fullns.split(".")[-1]

    def get_ns(self):
        return self.fullns

    def merge(self, to_merge):
        for name, pointer in to_merge.points_to.items():
            self.points_to[name].merge(pointer)


class DefinitionError(Exception):
    pass
