#!/usr/bin/env python3
"""核对入口位置表达式的边界，不依赖真实产物。"""
import unittest
from types import SimpleNamespace
from parameters import Locations


class Expressions(unittest.TestCase):
    def setUp(self):
        self.loc = Locations.__new__(Locations)
        self.loc.arch, self.loc.sp = 'x64', 7

    def decode(self, *ops, frame=None, cfa=None):
        return self.loc.decode([dict(op=n, args=a) for n, a in ops], cfa, frame)

    def test_pieces_keep_missing_bytes(self):
        p = self.decode(('DW_OP_reg5', []), ('DW_OP_piece', [8]), ('DW_OP_piece', [8]))
        self.assertEqual((p[0]['register'], p[0]['size_bits']), ('rdi', 64))
        self.assertEqual((p[1]['kind'], p[1]['value_bit_offset']), ('unknown', 64))

    def test_entry_sp_conversion(self):
        self.assertEqual(self.decode(('DW_OP_fbreg', [16]), frame=dict(entry_sp_offset=8))[0]['offset'], 24)
        self.assertEqual(self.decode(('DW_OP_call_frame_cfa', []), cfa=dict(entry_sp_offset=8))[0]['offset'], 8)
        self.assertEqual(self.decode(('DW_OP_fbreg', [16]))[0]['kind'], 'unknown')

    def test_changing_sp_frame_is_not_entry_sp(self):
        self.loc.select = lambda *args: ([87], 'expression')
        self.loc.operations = lambda raw: [dict(op='DW_OP_reg7', args=[])]
        self.loc.cfi = ([100, 101], [(100, 101, SimpleNamespace(expr=None, reg=7, offset=8)),
                                  (101, 110, SimpleNamespace(expr=None, reg=7, offset=32))])
        frame = self.loc.frame(None, 100, dict(entry_sp_offset=8, offset=8), [(100, 110)])
        self.assertIsNone(frame['entry_sp_offset'])
        self.assertFalse(frame['sp_stable'])

    def test_indirect_is_not_pointer_register(self):
        p = self.decode(('DW_OP_breg5', [0]))[0]
        self.assertEqual((p['kind'], p['register']), ('indirect', 'rdi'))
        self.assertEqual(self.decode(('DW_OP_reg5', []))[0]['kind'], 'register')

    def test_entry_value_is_not_current_location(self):
        p = self.decode(('DW_OP_entry_value', [[dict(op='DW_OP_reg5', args=[])]]), ('DW_OP_stack_value', []))[0]
        self.assertEqual(p['kind'], 'unknown')
        self.assertEqual(p['entry_value_pieces'][0]['register'], 'rdi')

    def test_unsupported_value_not_memory(self):
        self.assertEqual(self.decode(('DW_OP_breg5', [1]), ('DW_OP_stack_value', []))[0]['kind'], 'unknown')
        p = self.decode(('DW_OP_breg5', [0]), ('DW_OP_constu', [32]), ('DW_OP_shr', []), ('DW_OP_stack_value', []))[0]
        self.assertEqual((p['register'], p['location_bit_offset']), ('rdi', 32))


if __name__ == '__main__':
    unittest.main()
