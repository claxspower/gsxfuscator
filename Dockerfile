FROM python:3.12-slim
WORKDIR /app
COPY web/requirements.txt /app/web/requirements.txt
RUN pip install --no-cache-dir -r /app/web/requirements.txt \
    && groupadd -r gsx && useradd -r -g gsx -d /app gsx
COPY --chown=gsx:gsx web /app/web
COPY --chown=gsx:gsx v2 /app/v2
COPY --chown=gsx:gsx obfuscator /app/obfuscator
USER gsx
EXPOSE 8787
# The deployment platform must set GSX_BUILD_TOKEN as a secret and terminate HTTPS.
CMD ["python", "-u", "web/service.py", "--origin", "--host", "0.0.0.0", "--port", "8787"]
