import socket
import json
import os
from collections import deque


class Pytanque:
    def __enter__(self):
        self.socket.connect((self.host, self.port))
        return self

    def __init__(self, host: str, port: int):
        self.host = host
        self.port = port
        self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.queue = deque()
        self.file = None
        self.thm = None

    def query(self, msg, size: int = 1024):
        payload = (json.dumps(msg) + "\n").encode()
        self.socket.sendall(payload)
        resp = self.socket.recv(size)
        return json.loads(resp.decode())

    def current_state(self):
        return self.queue[-1]

    def start(self, *, file: str, thm: str):
        self.file = file
        self.thm = thm
        self.queue.clear()
        path = os.path.abspath(file)
        msg = ["Start", {"uri": f"file://{path}", "thm": thm}]
        [_, [_, state]] = self.query(msg)
        self.queue.append(state)
        print(self.current_state())

    def run_tac(self, tac: str):
        msg = ["Run_tac", {"st": self.current_state(), "tac": tac}]
        [_, [_, state]] = self.query(msg)
        self.queue.append(state)
        print(self.current_state())

    def rollback(self):
        self.queue.pop()

    def __exit__(self, exc_type, exc_value, exc_tb):
        self.socket.close()
