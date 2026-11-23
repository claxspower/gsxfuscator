from pathlib import Path
import re
import sys
import unittest
from html.parser import HTMLParser

ROOT = Path(__file__).resolve().parents[1]
class ScriptParser(HTMLParser):
    def __init__(self):
        super().__init__(); self.stack=[];self.scripts=[]
    def handle_starttag(self, tag, attrs):
        if tag=='script': self.stack.append('')
    def handle_data(self, data):
        if self.stack:self.stack[-1]+=data
    def handle_endtag(self, tag):
        if tag=='script': self.scripts.append(self.stack.pop())

class SafePublic(unittest.TestCase):
    def test_public_not_include_compiler(self):
        a=(ROOT/'pages/public/index.html').read_text()
        b=(ROOT/'worker/assets/index.html').read_text()
        self.assertEqual(a,b)
        for text in ('WORKER_B64','WASM_B64','DRIVER_B64','MODULES =','engineSrc',
                     'compiler-worker.js','wasmoon.LuaFactory','glue.wasm'):
            self.assertNotIn(text,a)
        self.assertIn("fetch('/api/build'",a)
        self.assertLess(len(a.encode()),200_000)
    def test_public_subdirectories_exclude_backend(self):
        for root in (ROOT/'pages/public',ROOT/'worker/assets'):
            self.assertEqual({x.name for x in root.iterdir()}, {'index.html','_headers','404.html'})
    def test_scripts_present(self):
        p=ScriptParser();p.feed((ROOT/'pages/public/index.html').read_text())
        self.assertGreaterEqual(len(p.scripts),3)
        self.assertTrue(any('compileFile(build)' in s for s in p.scripts))

if __name__=='__main__': unittest.main()
