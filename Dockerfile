# 使用官方提供的 Playwright Python 镜像作为基础
FROM mcr.microsoft.com/playwright/python:v1.40.0-jammy

# 设置工作目录
WORKDIR /app

# 更新包列表并安装 dumb-init（处理容器僵尸进程的关键）
# 并在安装完成后清理缓存，保持镜像精简
RUN apt-get update && apt-get install -y dumb-init && rm -rf /var/lib/apt/lists/*

# 拷贝项目文件
COPY requirements.txt .
COPY app.py .

# 安装 Python 依赖
RUN pip install --no-cache-dir -r requirements.txt

# 暴露 Flask 默认端口
EXPOSE 5000

# 使用 dumb-init 作为入口，确保进程信号正确传递及回收僵尸子进程
ENTRYPOINT ["/usr/bin/dumb-init", "--"]

# 运行整合了 Flask 和定时任务的脚本
CMD ["python", "-u", "app.py"]
