#!/usr/bin/env python3
"""从工程根目录运行一条命令，原样保存合并输出及执行元数据。仅用标准库。"""

import datetime
import json
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import time
from zoneinfo import ZoneInfo


def main():
    args = sys.argv[1:]
    # 旧命令仍记录到 v0.0.3；新阶段显式选择目录，不覆盖历史日志。
    stage = "v0.0.3"
    if args[:1] == ["--stage"]:
        if len(args) < 2:
            sys.exit("--stage 后需要版本号，例如 v0.1.1。")
        stage, args = args[1], args[2:]
    if not re.fullmatch(r"v[0-9]+\.[0-9]+(?:\.[0-9]+|_[A-Za-z0-9_-]+)", stage):
        sys.exit("阶段格式应为 v0.1.1 或 v0.4_alignment 等安全阶段名。")
    if len(args) < 2:
        sys.exit("用法: python3 scripts/run_logged.py [--stage v0.1.1] 标签 命令 [参数 ...]")
    label, *command = args
    if not re.fullmatch(r"[A-Za-z0-9_-]+", label):
        sys.exit("标签只允许英文字母、数字、下划线与连字符。")
    root = Path(__file__).resolve().parent.parent
    log_dir = root / "logs" / stage
    log_dir.mkdir(parents=True, exist_ok=True)
    started = datetime.datetime.now(ZoneInfo("Asia/Shanghai"))
    stem = started.strftime("%Y%m%dT%H%M%S_%f") + "_" + label
    output_path = log_dir / (stem + ".log")
    metadata_path = log_dir / (stem + ".json")
    metadata = {
        "stage": stage,
        "command": command,
        "command_display": shlex.join(command),
        "cwd": str(root),
        "executable": shutil.which(command[0]),
        "started_at": started.isoformat(),
        "output_file": output_path.name,
        "output_mode": "stdout and stderr merged, raw bytes",
        "exit_code": None,
        "status": "running",
    }
    metadata_path.write_text(json.dumps(metadata, ensure_ascii=False, indent=2) + "\n")
    clock_start = time.monotonic()
    print("日志:", output_path, flush=True)
    with output_path.open("xb") as output:
        try:
            process = subprocess.Popen(
                command, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT
            )
            # 不经 shell 执行参数；边读取边落盘，失败输出也保留。
            while True:
                chunk = process.stdout.read1(65536)
                if not chunk:
                    break
                output.write(chunk)
                output.flush()
                sys.stdout.buffer.write(chunk)
                sys.stdout.buffer.flush()
            code = process.wait()
        except OSError as error:
            message = (str(error) + "\n").encode("utf-8")
            output.write(message)
            sys.stderr.buffer.write(message)
            code = 127
    metadata.update(
        exit_code=code,
        status="finished",
        ended_at=datetime.datetime.now(ZoneInfo("Asia/Shanghai")).isoformat(),
        elapsed_seconds=round(time.monotonic() - clock_start, 3),
    )
    metadata_path.write_text(json.dumps(metadata, ensure_ascii=False, indent=2) + "\n")
    print("退出码:", code, "；元数据:", metadata_path, flush=True)
    return code if code >= 0 else 128 - code


if __name__ == "__main__":
    sys.exit(main())
